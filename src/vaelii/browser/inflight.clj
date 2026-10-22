;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.inflight
  "Page loads that run long: released from the request, joined rather than repeated, and
  listed while they run.

  A page is a read, and over a KB of millions of sentexes some reads run for minutes or
  more. Without this, the request holds its server thread for the whole read and the
  reader gets a spinner. A reader who clicks again, or reloads, starts a second read of
  the same page beside the first. Neither read can be stopped from outside: interrupting
  a thread inside a disk store's read closes the store's file channel. So the protection
  is to never start a second copy of a read, and to show what is running.

  - **Released.** A page load runs on a thread of its own, and the request waits for it
    `detach-ms` (`vaelii.browser.detach-ms`, 5 s). A page done by then is answered as
    usual. One that is not is answered with a page saying what is being computed and for
    how long. That page polls `/inflight/poll` and, once the read is done, loads the
    page's own URL again, which is then answered from the finished result.
  - **Joined.** A second load of the same URL and query in the same session while the
    first runs waits on the first instead of starting another. The read always computes
    the whole document, never the boosted fragment, so a boosted load and a plain reload
    of the same URL share one read (htmx selects `#main` out of a whole document).
  - **Kept.** A finished result nobody was waiting for is kept `keep-ms` for that next
    load, then dropped.
  - **Listed.** `running` is what `/jobs` lists: each read's URL, its age, and the
    engine frame its thread is in.

  Only a **page load** is guarded: a GET or HEAD that is a plain navigation or an htmx
  boosted one (`HX-Boosted`). Every other htmx request targets part of a page that has
  its own place to land, and a waiting page swapped into it would land in the wrong
  place. Static files (a last path segment holding a dot) and `/health` pass straight
  through."
  (:require [clojure.string :as str])
  (:import (java.util UUID)))

(def ^:private default-detach-ms 5000)

(defn detach-ms
  "How long a page load holds its request before it is answered with the waiting page:
  `vaelii.browser.detach-ms` when it parses to a positive integer, else 5 s."
  []
  (or (some-> (System/getProperty "vaelii.browser.detach-ms") str/trim parse-long
              (#(when (pos? %) %)))
      default-detach-ms))

(def keep-ms
  "How long a finished result that nobody was waiting for is kept for the load that comes
  back for it."
  300000)

;; :running — id → entry while its read runs; :finished — id → entry once done and not
;; yet taken.  An entry is {:id :key :uri :query :started :thread :future}, plus
;; :response and :done once finished.  Every transition holds `lock`.
(defonce ^:private state (atom {:running {} :finished {}}))
(defonce ^:private lock (Object.))

(defn- now [] (System/currentTimeMillis))

(defn- page-load? [{:keys [request-method uri headers]}]
  (and (#{:get :head} request-method)
       (or (nil? (get headers "hx-request")) (= "true" (get headers "hx-boosted")))
       (not (contains? #{"/health"} uri))
       (not (str/starts-with? uri "/inflight/"))
       (not (str/includes? (subs uri (inc (str/last-index-of uri "/"))) "."))))

(defn- request-key
  "What makes two loads the same read: the method, the URL, the query and the session,
  since a page reads the reader's own sandbox."
  [req session-of]
  [(:request-method req) (:uri req) (:query-string req) (session-of req)])

(def ^:private htmx-headers
  "The request headers that make a page answer as a fragment."
  ["hx-request" "hx-boosted" "hx-current-url" "hx-target" "hx-trigger" "hx-trigger-name"])

(defn- prune! []
  (let [cut (- (now) keep-ms)]
    (swap! state update :finished
           #(into {} (remove (fn [[_ e]] (< (long (:done e)) cut))) %))))

(defn- by-key [m k] (some (fn [[_ e]] (when (= k (:key e)) e)) m))

(defn- finished! [id resp]
  (locking lock
    (when-let [e (get-in @state [:running id])]
      (swap! state #(-> %
                        (update :running dissoc id)
                        ;; only a text body can be handed to a second reader: a stream is
                        ;; consumed by whichever writes it first
                        (cond-> (or (nil? (:body (:ok resp))) (string? (:body (:ok resp)))
                                    (:error resp))
                          (assoc-in [:finished id] (assoc e :response resp :done (now)))))))))

(defn- start! [h req k]
  (let [id     (str (UUID/randomUUID))
        thread (atom nil)
        fut    (future
                 (reset! thread (Thread/currentThread))
                 (let [r (try {:ok (h (apply update req :headers dissoc htmx-headers))}
                              (catch Throwable t {:error t}))]
                   (finished! id r)
                   r))
        e      {:id id :key k :uri (:uri req) :query (:query-string req) :started (now)
                :thread thread :future fut}]
    (swap! state assoc-in [:running id] e)
    e))

(defn- answer [{:keys [ok error]}]
  (if error (throw error) ok))

(defn- forget! [id]
  (locking lock (swap! state update :finished dissoc id)))

(defn href
  "The URL of a read: its page's own."
  [{:keys [uri query]}]
  (str uri (when (seq query) (str "?" query))))

(defn wrap
  "Guard `h`'s page loads (see the namespace doc). `waiting` renders the page a load past
  `detach-ms` is answered with: `(waiting req entry)`, `entry` carrying `:id`, `:uri`,
  `:query` and `:started`. `session-of` names the reader's session in a request."
  [h waiting session-of]
  (fn [req]
    (if-not (page-load? req)
      (h req)
      (let [k (request-key req session-of)
            [done e] (locking lock
                       (prune!)
                       (let [{:keys [running finished]} @state]
                         (if-let [f (by-key finished k)]
                           (do (swap! state update :finished dissoc (:id f)) [f nil])
                           [nil (or (by-key running k) (start! h req k))])))]
        (if done
          (answer (:response done))
          (let [r (deref (:future e) (detach-ms) ::pending)]
            (if (= ::pending r)
              (waiting req e)
              (do (forget! (:id e)) (answer r)))))))))

(defn status
  "`:running`, `:done` or nil (an id this process holds nothing for) for the read `id`."
  [id]
  (let [{:keys [running finished]} @state]
    (cond (contains? running id) :running
          (contains? finished id) :done)))

(defn- engine-frame
  "The innermost `vaelii` frame of `t`'s stack, as `ns/fn:line`, or nil."
  [^Thread t]
  (when t
    (some (fn [^StackTraceElement f]
            (let [c (.getClassName f)]
              (when (str/starts-with? c "vaelii.")
                (str (-> c (str/replace #"\$fn__\d+.*" "") (str/replace "$" "/")
                         (str/replace "_" "-"))
                     ":" (.getLineNumber f)))))
          (.getStackTrace t))))

(defn running
  "The page reads running now, oldest first: `{:id :uri :query :started :ms :frame}`, where
  `:frame` is the innermost engine frame its thread is in."
  []
  (->> (vals (:running @state))
       (sort-by :started)
       (mapv (fn [{:keys [thread started] :as e}]
               (-> (select-keys e [:id :uri :query :started])
                   (assoc :ms (- (now) (long started)) :frame (engine-frame @thread)))))))
