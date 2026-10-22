;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-lists-test
  "The lists (`/lists`): whole-KB lists of the defeats, the contradictions and the unary
  predicates with no genl but `thing`, each run as a read job from its button, and its
  rows paged."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;;   CxUniverse  (genl mammal_t thing) (genl dog_t mammal_t) (disjoint mammal_t reptile_t)
;;     ├─ CxL    (reptile_t Rex) default
;;     └─ CxR    (dog_t Rex) monotonic
;;   CxJ sees CxL and CxR, so the default member is defeated there.
;;   (wobbles W) and (not (wobbles W)) at one strength: a represented dilemma.
;;   lonely_t declares no genl, thingly_t only (genl thingly_t thing).
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/fresh) tu/load-core!)]
      (doseq [[c up] '[[CxL CxUniverse] [CxR CxUniverse] [CxJ CxL] [CxJ CxR]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [s '[(genl mammal_t thing) (genl dog_t mammal_t) (disjoint mammal_t reptile_t)
                  (unary_predicate lonely_t) (unary_predicate thingly_t)
                  (genl thingly_t thing)]]
        (v/assert kb s 'CxUniverse))
      (v/assert kb '(reptile_t Rex) 'CxL)
      (v/assert kb '(dog_t Rex) 'CxR {:strength :monotonic})
      (v/assert kb '(wobbles W) 'CxDilemma)
      (v/assert kb '(not (wobbles W)) 'CxDilemma)
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (jobs/reset-registry!)
               (catalog/reset-registry!)
               (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params]
  (*app* {:request-method :post :uri uri :scheme :http :params params :headers {}}))

(defn- run-list [which]
  (POST "/lists/run" {"list" which}))

(deftest the-page-reads-nothing-until-a-button-is-pressed
  (let [b (:body (GET "/lists"))]
    (is (re-find #"Defeats" b))
    (is (re-find #"Contradictions" b))
    (is (re-find #"Unary predicates without a genl" b))
    (is (empty? (jobs/jobs)) "no list ran")
    (is (re-find #"href=\"/lists\"" (:body (GET "/"))) "the menubar links it")))

(deftest the-defeats-list-holds-the-defeated-sentex
  (let [r (run-list "defeats")
        j (first (jobs/jobs))]
    (is (= 200 (:status r)))
    (is (= :list (:kind j)))
    (is (= :done (:status j)))
    (is (= (count (v/sentexes-with-functor tu/*kb* 'defeat {:believed? true}))
           (:rows (:summary j))))
    (is (pos? (:rows (:summary j))))
    (is (re-find #"reptile_t" (:body r)))
    (is (re-find #"the defeat" (:body r)))
    (is (= (str "/lists/result?job=" (:id j)) (get-in r [:headers "HX-Push-Url"])))
    (testing "the result has a page of its own, and the lists page links it"
      (is (re-find #"reptile_t" (:body (GET "/lists/result" (str "job=" (:id j))))))
      (is (re-find #"Last run" (:body (GET "/lists")))))))

(deftest the-contradictions-list-holds-dilemmas-and-conflicts
  (run-list "contradictions")
  (let [j (first (jobs/jobs))
        b (:body (GET "/lists/result" (str "job=" (:id j))))]
    (is (= (+ (count (v/contradictions tu/*kb*)) (count (v/conflicts tu/*kb*)))
           (:rows (:summary j))))
    (is (re-find #"dilemma" b))
    (is (re-find #"wobbles" b))
    (is (not-any? :grounds (:rows (meta (:summary j)))) "the rows are read without grounds")))

(deftest the-clash-reports-leave-their-grounds-off-when-asked
  (let [kb tu/*kb*
        ds (v/contradictions kb)]
    (is (seq ds))
    (is (every? #(contains? % :grounds) ds))
    (is (= (map #(dissoc % :grounds) ds) (v/contradictions kb nil {:grounds? false})))
    (is (= (v/contradictions kb) (v/contradictions kb nil {:grounds? true})))
    (is (= (map #(dissoc % :grounds) (v/conflicts kb)) (v/conflicts kb {:grounds? false})))
    (testing "a misspelt or mistyped option is refused rather than read as the default"
      (is (= :unknown-option (:type (ex-data (try (v/conflicts kb {:grounds false})
                                                  (catch Exception e e))))))
      (is (= :unknown-option (:type (ex-data (try (v/contradictions kb nil {:grounds? "no"})
                                                  (catch Exception e e)))))))))

(deftest a-types-stored-members-are-read-off-the-index
  (let [kb tu/*kb*]
    (is (= #{'lonely_t 'thingly_t}
           (into #{} (filter '#{lonely_t thingly_t}) (v/stored-first-args kb 'unary_predicate))))
    (is (contains? (v/stored-first-args kb 'reptile_t) 'Rex)
        "a membership defeated in one context is still stored")
    (is (empty? (v/stored-first-args kb 'no_such_type_t)))))

(deftest the-orphan-list-holds-types-with-no-genl-but-thing
  (run-list "orphan-types")
  (let [j     (first (jobs/jobs))
        terms (set (map :term (:rows (meta (:summary j)))))]
    (is (= :done (:status j)))
    (is (contains? terms 'lonely_t) "no genl at all")
    (is (contains? terms 'thingly_t) "genl thing only")
    (is (not (contains? terms 'dog_t)) "a genl below thing")
    (is (not (contains? terms 'thing)) "the root is not an orphan")
    (is (re-find #"genl thing only" (:body (GET "/lists/result" (str "job=" (:id j))))))))

(deftest rows-continue-a-page-at-a-time
  (run-list "orphan-types")
  (let [j (first (jobs/jobs))
        n (:rows (:summary j))]
    (is (= 200 (:status (GET "/lists/rows" (str "job=" (:id j) "&offset=0")))))
    (is (= (min n 200)
           (count (re-seq #"<li>" (:body (GET "/lists/rows" (str "job=" (:id j) "&offset=0")))))))
    (is (= 400 (:status (GET "/lists/rows" (str "job=" (:id j) "&offset=x")))))
    (is (re-find #"gone" (:body (GET "/lists/rows" "job=nope&offset=0"))))))

(deftest a-bad-list-or-a-gone-job-is-said-so
  (is (= 400 (:status (run-list "everything"))))
  (is (empty? (jobs/jobs)))
  (is (re-find #"is gone" (:body (GET "/lists/result" "job=nope")))))

(deftest a-cross-origin-run-is-refused
  (is (= 403 (:status (*app* {:request-method :post :uri "/lists/run" :scheme :http
                              :params {"list" "defeats"}
                              :headers {"origin" "http://evil.example"
                                        "host" "localhost"}}))))
  (is (empty? (jobs/jobs))))
