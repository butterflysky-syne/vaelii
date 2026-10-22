;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.removed
  "The sentexes the browser last removed from each KB, so a removal can be put back.

  A retraction is the browser's one write that loses content: an assert can be retracted
  and an edit edited back, but a retracted sentence exists afterwards only in the reader's
  memory.  So every removal the browser makes is noted here first — the sentence as the
  editor prints it, its context and its strength — and the newest `max-kept` per KB are
  kept.  `/removed` lists them, and putting one back is an assert of what was noted.

  **Per KB, by name, on disk.**  The list is about a KB rather than a session, it has to
  outlive the process that made the removal, and it must not be written into the KB it
  describes, so it is an EDN file per KB under `~/.vaelii/removed/` (the `vaelii.removed.dir`
  property moves it, and the test profile sets it).  A file is
  replaced whole through a rename, so a reader never sees half of one.

  Only the sentexes a removal **took out** are noted.  A selected sentex that stays,
  being derived another way, was not lost, and the derived sentexes the sweep took with a
  removal come back with what they rest on."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import (java.io File)
           (java.nio.file Files StandardCopyOption)
           (java.time Instant)
           (java.util UUID)))

(def max-kept
  "How many removals each KB's list holds; a note past it drops the oldest."
  50)

(defn- set-to [s] (when-not (str/blank? s) s))

(defn- dir ^File []
  (io/file (or (set-to (System/getProperty "vaelii.removed.dir"))
               (str (System/getProperty "user.home") "/.vaelii/removed"))))

(defn- file-for
  "The list's file for the KB named `kb-name`.  The name is a label anyone can give a
  KB, so everything outside `[A-Za-z0-9._-]` becomes `_` before it names a file."
  ^File [kb-name]
  (io/file (dir) (str (str/replace (str kb-name) #"[^A-Za-z0-9._-]" "_") ".edn")))

;; reads and writes of every list are one at a time: a note is a read-modify-write of the
;; file, and two removals landing together must not drop each other's entries
(defonce ^:private file-monitor (Object.))

(defn entries
  "The removals noted for the KB named `kb-name`, newest first: `{:id :at :sentence
  :context :strength :via}`, where `:sentence` and `:context` are text as the editor
  prints them.  A missing or unreadable file is an empty list."
  [kb-name]
  (locking file-monitor
    (let [f (file-for kb-name)]
      (if (.exists f)
        (try (vec (edn/read-string (slurp f)))
             (catch Exception _ []))
        []))))

(defn- write-entries [kb-name es]
  (let [f   (file-for kb-name)
        tmp (io/file (.getParentFile f) (str "." (.getName f) ".tmp"))]
    (io/make-parents f)
    (binding [*print-length* nil *print-level* nil *print-meta* false]
      (spit tmp (pr-str (vec es))))
    (Files/move (.toPath tmp) (.toPath f)
                (into-array [StandardCopyOption/REPLACE_EXISTING
                             StandardCopyOption/ATOMIC_MOVE]))))

(defn note!
  "Prepend `rows` (`{:sentence :context :strength}`, text) to the KB's list, each given an
  id, the time and `via` (what removed it: `:retract`, `:edit`, `:term`), and
  keep the newest `max-kept`.  Answers the rows as noted."
  [kb-name via rows]
  (if (empty? rows)
    []
    (locking file-monitor
      (let [at    (str (Instant/now))
            noted (mapv #(assoc % :id (str (UUID/randomUUID)) :at at :via via) rows)]
        (write-entries kb-name (take max-kept (concat noted (entries kb-name))))
        noted))))

(defn entry
  "The noted removal `id` in the KB's list, or nil."
  [kb-name id]
  (some #(when (= id (:id %)) %) (entries kb-name)))

(defn forget!
  "Drop the noted removal `id` from the KB's list — once it has been put back."
  [kb-name id]
  (locking file-monitor
    (write-entries kb-name (remove #(= id (:id %)) (entries kb-name)))))
