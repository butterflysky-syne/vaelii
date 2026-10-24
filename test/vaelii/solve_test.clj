;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-test
  "`vaelii.impl.solve`: `program`'s split of contested assumptions from fixed background,
  `content-key`'s order independence, and `local-solver`'s decisions, over hand-built
  `Program` values.  The last section checks the stub is a fresh KB's solver and that
  `set-solver` replaces it."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

;; ---- builders ------------------------------------------------------------
;;
;; Sentences are `(a)`, `(b)`, …, so the content order is the sentence order, and every
;; expectation names a claim, never a handle.

(defn- content
  "Handle → what it asserts, from `handle sentence` pairs, all in one context."
  [& pairs]
  (into {} (map (fn [[h s]] [h {:sentence s :context 'C}])) (partition 2 pairs)))

(defn- ng
  "A nogood map, `{:nogood :priority :sentence}`, as `clashes/contradictions-of` builds."
  [priority & handles]
  {:nogood (set handles) :priority priority :sentence (list 'contradicts handles)})

(defn- decide [program] (solve-types/solve solve/local-solver program))

(defn- claims
  "What `handles` assert, per `content`."
  [content handles]
  (into #{} (map #(get-in content [% :sentence])) handles))

;; ---- 1. Program: the split between decidable and fixed -------------------

(deftest program-splits-contested-assumptions-from-fixed-background
  (let [c (content 1 '(a) 2 '(b) 9 '(z))
        p (solve/program #{1 2} [(ng 0 1 2) (ng 0 2 9)] c)]
    (testing "only the contested handles are assumptions"
      (is (= #{1 2} (:assumptions p))))
    (testing "the uncontested member of a relevant nogood is fixed background"
      (is (= #{9} (:fixed p))))
    (testing "and the fixed handle's content is withheld — it is not up for decision"
      (is (= #{1 2} (set (keys (:content p)))))
      (is (nil? (get-in p [:content 9]))))
    (testing "both nogoods are relevant: each touches a contested handle"
      (is (= 2 (count (:contradictions p)))))))

(deftest program-drops-a-nogood-with-no-contested-member
  (let [p (solve/program #{1} [(ng 0 1 2) (ng 5 7 8)] (content 1 '(a) 2 '(b) 7 '(c) 8 '(d)))]
    (is (= [#{1 2}] (mapv :nogood (:contradictions p))))
    (is (= #{2} (:fixed p)) "7 and 8 are not background to anything the solver sees")))

(deftest an-empty-program-decides-nothing
  ;; a plug-in solver may be handed one
  (let [p (solve/program #{} [] {})]
    (is (= #{} (:assumptions p)))
    (is (= #{} (:fixed p)))
    (is (= [] (:contradictions p)))
    (is (= {} (:content p)))
    (is (= {:defeat #{} :violated []} (decide p)))))

(deftest a-neg-nogood-is-an-at-least-one
  (let [c (content 1 '(a) 2 '(b))]
    (testing "a satisfied at-least-one is skipped, not violated"
      (let [p (solve/program #{1 2}
                             [{:neg #{1 2} :priority 0 :sentence '(atleastone)}]
                             c)]
        (is (= {:defeat #{} :violated []} (decide p)))))
    (testing "a fixed member satisfies it permanently"
      (let [p (solve/program #{1}
                             [{:neg #{1 2} :priority 0 :sentence '(atleastone)}]
                             c)]
        (is (= #{2} (:fixed p)) "handle 2 is background, assumed true")
        (is (= {:defeat #{} :violated []} (decide p)))))
    (testing "a mixed nogood defeats its positive member, never reads :neg as positive"
      ;; forbidden: (a) held while (b) absent; (b) is believed, so the body never holds
      (let [p (solve/program #{1 2}
                             [{:nogood #{1} :neg #{2} :priority 0 :sentence '(implic)}]
                             c)]
        (is (= {:defeat #{} :violated []} (decide p)))))))

;; ---- 2. content-key: the order-independence primitive --------------------

(deftest content-key-orders-on-the-claim-not-on-the-handle
  (let [p1 (solve/program #{1 2} [] (content 1 '(a) 2 '(b)))
        p2 (solve/program #{1 2} [] (content 1 '(b) 2 '(a)))
        key1 #(solve/content-key p1 %)
        key2 #(solve/content-key p2 %)]
    (testing "in p1 the claim (a) sits on handle 1 and sorts first"
      (is (neg? (compare (key1 1) (key1 2)))))
    (testing "in p2 it sits on handle 2 and still sorts first"
      (is (neg? (compare (key2 2) (key2 1)))))
    (testing "because the claim leads the key and the handle only trails it"
      (is (str/starts-with? (key1 1) "[(a) C "))
      (is (str/starts-with? (key2 2) "[(a) C "))
      (is (not= (key1 1) (key2 2))
          "the two keys do differ — in the trailing handle, which is why it must be last"))))

(deftest content-key-separates-the-same-sentence-in-different-contexts
  (let [p (solve/program #{1 2} []
                         {1 {:sentence '(a) :context 'C}
                          2 {:sentence '(a) :context 'D}})]
    (is (not= (solve/content-key p 1) (solve/content-key p 2)))))

(deftest content-key-falls-back-to-the-handle-only-for-identical-content
  (let [p (solve/program #{1 2} [] (content 1 '(a) 2 '(a)))]
    (is (not= (solve/content-key p 1) (solve/content-key p 2)))
    (is (neg? (compare (solve/content-key p 1) (solve/content-key p 2))))))

(deftest content-key-is-total-over-handles-the-program-has-no-content-for
  ;; a fixed member carries no content, and the nogood order key maps over every member
  (let [p (solve/program #{1} [(ng 0 1 9)] (content 1 '(a) 9 '(z)))]
    (is (string? (solve/content-key p 9)))
    (is (not= (solve/content-key p 9) (solve/content-key p 8))
        "distinct unknown handles still get distinct keys")))

;; ---- 3. local-solver: the decision ---------------------------------------

(deftest a-two-way-tie-defeats-exactly-one-side
  (let [c (content 1 '(a) 2 '(b))
        r (decide (solve/program #{1 2} [(ng 0 1 2)] c))]
    (testing "one of the two contested defaults gives way, not both and not neither"
      (is (= 1 (count (:defeat r)))))
    (testing "and it is the greatest content-key — the claim (b)"
      (is (= #{'(b)} (claims c (:defeat r)))))
    (testing "with nothing left unsatisfiable"
      (is (= [] (:violated r))))))

(deftest the-same-claim-loses-under-any-handle-numbering
  (let [c1 (content 1 '(a) 2 '(b))
        c2 (content 1 '(b) 2 '(a))
        r1 (decide (solve/program #{1 2} [(ng 0 1 2)] c1))
        r2 (decide (solve/program #{1 2} [(ng 0 1 2)] c2))]
    (is (= 1 (count (:defeat r1))))
    (is (= 1 (count (:defeat r2))))
    (testing "the same claim loses both times"
      (is (= (claims c1 (:defeat r1)) (claims c2 (:defeat r2)))))
    (testing "though a different handle carries it — otherwise the test proves nothing"
      (is (not= (:defeat r1) (:defeat r2))))))

(deftest the-result-does-not-depend-on-the-order-the-nogoods-arrive-in
  ;; an earlier choice constrains every later one, so the walk order must not be the
  ;; input order
  (let [c  (content 1 '(a) 2 '(b) 3 '(c))
        as (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 2 3)] c))
        bs (decide (solve/program #{1 2 3} [(ng 0 2 3) (ng 0 1 2)] c))]
    (is (= as bs))
    (is (seq (:defeat as)) "and it actually decided something")))

;; ---- 4. what may be defeated ---------------------------------------------

(deftest only-a-contested-member-is-ever-defeated
  ;; the fixed member carries the greater content-key, so a stub ignoring
  ;; `:assumptions` would pick it
  (let [c (content 1 '(a) 9 '(z))
        p (solve/program #{1} [(ng 0 1 9)] c)
        r (decide p)]
    (is (= #{9} (:fixed p)) "the setup really does put the bigger key on the fixed side")
    (is (= #{1} (:defeat r)))
    (is (= [] (:violated r)))))

(deftest a-nogood-with-no-choosable-member-is-reported-violated
  ;; `program` filters such a nogood out, so only a hand-built Program carries one
  (let [bad (ng 3 7 8)
        r   (solve-types/solve solve/local-solver
                               (solve-types/->Program #{} #{7 8} [bad] {} []))]
    (is (= #{} (:defeat r)))
    (is (= [bad] (:violated r)) "the whole nogood map comes back, not just its handles")))

(deftest a-violated-nogood-does-not-stop-the-satisfiable-ones
  (let [c   (content 1 '(a))
        bad (ng 0 7 8)
        r   (solve-types/solve solve/local-solver
                               (solve-types/->Program #{1} #{7 8 9} [(ng 0 1 9) bad] c []))]
    (is (= #{1} (:defeat r)))
    (is (= [bad] (:violated r)))))

;; ---- 5. priority, and the already-satisfied skip -------------------------

(deftest the-highest-priority-nogood-is-decided-first
  ;; both orderings, since only the pair tells the sort key from its negation
  (let [c (content 1 '(a) 2 '(b) 3 '(c))]
    (testing "with the {1,2} pair ranked first, giving up (b) settles both"
      (let [r (decide (solve/program #{1 2 3} [(ng 10 1 2) (ng 0 2 3)] c))]
        (is (= #{'(b)} (claims c (:defeat r))))))
    (testing "with the {2,3} pair ranked first, the greedy walk costs a second datum"
      (let [r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 10 2 3)] c))]
        (is (= #{'(b) '(c)} (claims c (:defeat r))))))))

(deftest a-nogood-already-satisfied-by-an-earlier-choice-is-skipped
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 2 3)] c))]
    (is (= #{'(b)} (claims c (:defeat r))) "one defeat satisfies both")
    (is (= [] (:violated r)) "a satisfied nogood is not a violated one")))

(deftest a-wider-nogood-is-satisfied-by-one-defeated-member
  ;; a nogood is satisfied once one member is out: {2,3,4} with (b) defeated still has
  ;; two members believed, and a pair-shaped `(<= (count live) 1)` check defeats (d) too
  (let [c (content 1 '(a) 2 '(b) 3 '(c) 4 '(d))
        r (decide (solve/program #{1 2 3 4} [(ng 0 1 2) (ng 0 2 3 4)] c))]
    (is (= #{'(b)} (claims c (:defeat r)))
        "defeating (b) satisfies both nogoods; (d) must survive")
    (is (= [] (:violated r)))))

(deftest a-wide-nogood-standing-alone-still-costs-one-defeat
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2 3)] c))]
    (is (= #{'(c)} (claims c (:defeat r))))
    (is (= [] (:violated r)))))

(deftest the-stub-is-greedy-and-not-globally-minimal
  ;; `asp_edge_test/defeat-is-minimal-across-overlapping-nogoods` runs the same shape on
  ;; the ASP backend and gets the one-atom cover
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 1 3)] c))]
    (is (= #{'(b) '(c)} (claims c (:defeat r))))
    (is (= [] (:violated r)) "suboptimal, but it did satisfy both")))

(deftest a-solve-is-a-pure-function-of-its-program
  ;; compared against a Program rebuilt field for field and one written in another order
  (let [c        (content 1 '(a) 2 '(b) 3 '(c))
        p        (solve/program #{1 2 3} [(ng 1 1 2) (ng 0 2 3)] c)
        recorded (solve-types/map->Program (into {} p))
        other    (solve/program #{3 2 1} [(ng 0 3 2) (ng 1 2 1)]
                                (content 3 '(c) 2 '(b) 1 '(a)))
        r        (decide p)]
    (is (not (identical? p recorded)))
    (is (= p recorded) "a Program is a value, so it reconstructs field for field")
    (is (= r (decide recorded)) "the recorded Program decides what the original did")
    (is (= r (decide other)) "and so does the same program written down in another order")
    (is (= #{'(b)} (claims c (:defeat r))) "the content-sort loser, in every ordering")
    (is (= #{:defeat :violated} (set (keys r))) "and the result shape is closed")))

;; ---- 6. the protocol on a live KB --------------------------------------------

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb the-shipped-default-solver-is-the-local-stub
  (is (identical? solve/local-solver @(:solver kb))))

(tu/deftest-kb set-solver-installs-the-solver-and-returns-the-kb
  ;; `nmtms_test/an-installed-solver-is-never-asked-to-decide-a-plain-rebuttal` checks
  ;; that a settle never asks it
  (let [asked  (atom [])
        plugin (reify solve-types/Solver
                 (solve [_ program]
                   (swap! asked conj program)
                   {:defeat #{} :violated []}))
        ret    (v/set-solver kb plugin)]
    (is (identical? kb ret) "set-solver is threadable")
    (is (identical? plugin @(:solver kb)))
    (testing "and the installed solver is what a solve dispatches to"
      (let [p (solve/program #{1 2} [(ng 0 1 2)] (content 1 '(a) 2 '(b)))]
        (is (= {:defeat #{} :violated []} (solve-types/solve @(:solver kb) p)))
        (is (= [p] @asked) "the plug-in saw the program, unaltered")))
    (testing "whereas the stub it replaced would have decided that same program"
      (is (= #{2} (:defeat (decide (solve/program #{1 2} [(ng 0 1 2)]
                                                  (content 1 '(a) 2 '(b))))))))))
