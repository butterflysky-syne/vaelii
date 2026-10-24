;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-branches-test
  "The planner's arm for fewer than two reorderable generators with a recursive literal
  present (`plan-pairs`), and an evaluable run unbound: an unbound goal answers empty,
  and an unbound rule antecedent is refused at assert."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the short-circuit arm, with a recursive literal in play ----------------

(tu/deftest-kb one-generator-plus-a-recursive-literal-still-pulls-the-deferred-forward
  ;; One generator and a recursive literal: the deferred literal lands between them.
  (tu/with-terms [step reaches Aa Bb CxPlan]
    (v/assert kb (list step Aa Bb) CxPlan)
    (let [gen (list step '?x '?y)
          rec (list reaches '?y '?z)
          flt (list 'lessThan '?x '?y)
          ordered (plan/order kb [gen rec flt] CxPlan {:consequent-pred reaches})]
      (testing "the deferred literal sits behind its binder and ahead of the recursion"
        (is (= [gen flt rec] ordered)))
      (testing "and nothing is dropped or duplicated by the reassembly"
        (is (= 3 (count ordered)))
        (is (= (frequencies [gen rec flt]) (frequencies ordered))))
      (testing "an evaluate is ready once its inputs are bound, its output aside"
        (let [ev (list 'evaluate '?z (list '+ '?x 1))]
          (is (= [gen ev rec] (plan/order kb [gen rec ev] CxPlan {:consequent-pred reaches}))))))))

(tu/deftest-kb a-deferred-literal-the-recursion-binds-stays-after-the-recursion
  ;; `?z` is bound by the recursive literal alone, so `early` is empty.
  (tu/with-terms [step reaches Aa Bb CxPlan]
    (v/assert kb (list step Aa Bb) CxPlan)
    (let [gen (list step '?x '?y)
          rec (list reaches '?y '?z)
          flt (list 'lessThan '?y '?z)
          ordered (plan/order kb [gen rec flt] CxPlan {:consequent-pred reaches})]
      (testing "an unbindable test cannot be pulled forward past what binds it"
        (is (= [gen rec flt] ordered)))
      (is (= 3 (count ordered))))))

(tu/deftest-kb with-no-generators-at-all-a-ready-deferred-literal-still-overtakes-the-recursion
  ;; `gens` empty; the variables arrive from the caller's `:bound`.
  (tu/with-terms [reaches CxPlan]
    (let [rec (list reaches '?y '?z)
          flt (list 'lessThan '?x '?y)
          ordered (plan/order kb [rec flt] CxPlan
                              {:consequent-pred reaches :bound '#{?x ?y}})]
      (is (= [flt rec] ordered))
      (is (= 2 (count ordered))))))

;; ---- an evaluable that actually runs unbound --------------------------------
;; docs/inference.md: a hoisted `evaluate` yields no solutions rather than an error.

(tu/deftest-kb an-unbound-evaluate-yields-no-solutions-rather-than-throwing
  ;; `eval-expr` reaches its ::fail arm on the unbound symbol.
  (tu/with-terms [CxEval]
    (is (empty? (v/ask kb (list 'evaluate '?z (list '+ '?q 1)) CxEval)))
    (testing "and nested one level down, where the failure has to propagate outward"
      (is (empty? (v/ask kb (list 'evaluate '?z (list '* 2 (list '+ '?q 1))) CxEval))))
    (testing "the ground form of the same expression does compute — this is not
              vacuous"
      (is (= [3] (map #(get % '?z)
                      (v/ask kb (list 'evaluate '?z (list '+ 2 1)) CxEval)))))))

(tu/deftest-kb an-unbound-comparison-yields-no-solutions-rather-than-throwing
  ;; `EvaluableProver` refuses a goal whose arguments are not all numbers.
  (tu/with-terms [CxEval]
    (is (empty? (v/ask kb (list 'lessThan '?n 35) CxEval)))
    (is (empty? (v/ask kb (list 'greaterThan '?n 35) CxEval)))
    (testing "the ground comparison still answers"
      (is (seq (v/ask kb (list 'lessThan 1 35) CxEval)))
      (is (empty? (v/ask kb (list 'lessThan 35 1) CxEval))))))

;; A rule antecedent nothing binds is refused at assert (`sentex/check-naf-closed`):
;; stored, it would answer empty backward and throw forward (`chain/solve-deferred`).

(tu/deftest-kb a-rule-antecedent-nothing-binds-is-refused-rather-than-stored
  ;; `?m` appears in no other antecedent.
  (tu/with-terms [age young Tom Bob CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (v/assert kb (list age Bob 40) CxPlan)
    (let [before (v/sentex-count kb)
          e (try (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?m 35)]
                                (list young '?p) CxPlan {:direction :backward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "nothing in the rule writes ?m")
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?m] (:unbound (ex-data e))))
      ;; `handle-of` would build the refused form, so the probe is the count
      (is (= before (v/sentex-count kb)) "a refused rule stores nothing"))
    (testing "the bound comparison is stored and runs, so this is not vacuous"
      (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?n 35)]
                     (list young '?p) CxPlan {:direction :backward})
      (is (= #{Tom} (set (map #(get % '?p)
                              (v/query kb (list young '?p) CxPlan {:max-depth 2})))))
      (testing "and identically with the planner inert"
        (is (= #{Tom} (binding [plan/*enabled* false]
                        (set (map #(get % '?p)
                                  (v/query kb (list young '?p) CxPlan
                                           {:max-depth 2}))))))))))

(tu/deftest-kb an-evaluate-antecedent-nothing-binds-is-refused-too
  ;; `evaluate` writes its first argument and reads the rest, so `?z` is not an input
  ;; and `?q` is — the split `sentex/deferred-input-vars` makes.
  (tu/with-terms [age bumped Tom CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (let [e (try (v/assert-rule kb [(list age '?p '?n) (list 'evaluate '?z (list '+ '?q 1))]
                                (list bumped '?p) CxPlan {:direction :backward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?q] (:unbound (ex-data e)))
          "?z is the output and is not required to be bound"))
    (testing "binding the expression's variable from the other antecedent stores it"
      (tu/with-terms [lifted]
        (v/assert-rule kb [(list age '?p '?n) (list 'evaluate '?z (list '+ '?n 1))]
                       (list lifted '?p) CxPlan {:direction :backward})
        (is (= #{Tom} (set (map #(get % '?p)
                                (v/query kb (list lifted '?p) CxPlan
                                         {:max-depth 2})))))))))

(tu/deftest-kb one-evaluate-may-feed-another-but-only-downhill
  ;; A deferred literal's output binds the ones written *after* it, because that is the
  ;; order the join runs them in: `plan/order` keeps deferred literals where the author
  ;; put them.  The placement phase that runs an aggregate keeps written order too.
  (tu/with-terms [age chained Tom CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (testing "written in dependency order, the chain runs"
      (v/assert-rule kb [(list age '?p '?n)
                         (list 'evaluate '?q (list '+ '?n 1))
                         (list 'evaluate '?z (list '* '?q 2))]
                     (list chained '?p '?z) CxPlan {:direction :backward})
      (is (= [62] (map #(get % '?z)
                       (v/query kb (list chained Tom '?z) CxPlan {:max-depth 2})))))
    (testing "written the other way up, it is refused rather than run unbound"
      (tu/with-terms [uphill]
        (let [e (try (v/assert-rule kb [(list age '?p '?n)
                                        (list 'evaluate '?z (list '* '?q 2))
                                        (list 'evaluate '?q (list '+ '?n 1))]
                                    (list uphill '?p '?z) CxPlan {:direction :backward})
                     nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e))
          (is (= :naf-not-closed (:type (ex-data e))))
          (is (= '[?q] (:unbound (ex-data e)))))))))
