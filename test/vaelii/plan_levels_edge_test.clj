;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-levels-edge-test
  "The planner's costing of a negative literal and of a ground argument after a
  variable, `escalate` from a floor above the answering level, and level 1 with no root
  to narrow on."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.test-util :as tu]))

;; The ranking is forced on: these tests measure the ranking, which `VAELII_PLAN=0`
;; removes (`tu/shipped-fixture`).
(use-fixtures :each (tu/neutral-fresh tu/fresh) (tu/shipped-fixture [#'plan/*enabled*]))

;; ---- the negative-literal cost path ------------------------------------

(tu/deftest-kb a-negative-literal-is-costed-by-the-predicate-extent
  ;; `count-at` answers 0 under `[:false <body>]`; the predicate extent counts both
  ;; polarities.
  (tu/with-terms [banned allowed Aa Bb Cc Dd]
    (doseq [i [Aa Bb Cc Dd]]
      (v/assert kb (list 'not (list banned i)) 'CxNaturalWorld {:chain? false}))
    (v/assert kb (list allowed Aa) 'CxNaturalWorld {:chain? false})
    (let [neg-cost (plan/est-matches kb (list 'not (list banned '?x)) #{})
          pos-cost (plan/est-matches kb (list allowed '?y) #{})]
      (testing "the negative literal's cost reflects its real extent, not zero"
        (is (pos? neg-cost) "a zero estimate would rank it as the cheapest literal")
        (is (>= neg-cost 4) "there are four stored negative facts"))
      (testing "and it is correctly costed as the more expensive of the two"
        (is (> neg-cost pos-cost)))
      (testing "so the positive literal leads"
        (is (= (list allowed '?x)
               (first (plan/order kb [(list 'not (list banned '?x)) (list allowed '?x)]
                                  'CxNaturalWorld))))))))

;; ---- the argument-root estimate ----------------------------------------

(tu/deftest-kb a-ground-argument-after-a-variable-is-costed-by-the-argument-root
  ;; The trie counts `(parentOf ?x Cid)` only up to `?x`; the argument root
  ;; `[parentOf 2 Cid]` counts the ground argument.
  (tu/with-terms [parentOf Ann Bob Cid Dee Eve]
    (doseq [[p c] [[Ann Bob] [Ann Cid] [Dee Eve] [Bob Eve] [Cid Eve]]]
      (v/assert kb (list parentOf p c) 'CxNaturalWorld {:chain? false}))
    (let [open      (plan/est-matches kb (list parentOf '?x '?y) #{})
          after-var (plan/est-matches kb (list parentOf '?x Cid) #{})]
      (testing "fixing the second argument is tighter than leaving both open"
        (is (< after-var open)
            "without the argument root this would be the same count as the open literal"))
      (is (<= after-var 1) "exactly one fact has Cid in argument 2"))))

;; ---- escalate's floor ---------------------------------------------------

(tu/deftest-kb escalate-starting-above-where-the-answer-lives
  ;; A floor above the answering level: `:tried` starts at the floor.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxNaturalWorld)
    (let [low  (v/escalate kb (list dog Muffet) 'CxNaturalWorld)
          high (v/escalate kb (list dog Muffet) 'CxNaturalWorld 5)]
      (testing "from the default floor the cheapest answering level is found"
        (is (some? (:level low)))
        (is (>= (:level low) 2)))
      (testing "from a floor of 5 the search starts there and still answers"
        (is (some? (:level high)))
        (is (>= (:level high) 5) "it never reports a level below the floor")
        (is (every? #(>= % 5) (:tried high))
            ":tried records only the levels actually attempted")))))

;; ---- level 1 with nothing to drive it ----------------------------------

(tu/deftest-kb level-one-with-no-root-to-narrow-on-yields-nothing
  ;; A variable context and a variable functor leave level 1 no root to narrow on.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxNaturalWorld)
    (is (empty? (v/lookup kb 1 '(?p ?x) '?ctx))
        "nothing names a root, so level 1 has nothing to offer")))
