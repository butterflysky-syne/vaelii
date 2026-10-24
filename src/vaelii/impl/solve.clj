;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.solve
  "The `Program` builder and the local solver behind `vaelii.impl.types.solve/Solver`:
  `program` builds the `Program` a labeling hands a solver, `content-key` orders contested
  assumptions by what they assert, and `local-solver` is the deterministic greedy stub.  The
  ASP backend is `vaelii.impl.asp.edge/edge-solver`.  See docs/asp.md and docs/nmtms.md,
  \"Only `:default` content reaches a solver\"."
  (:require [clojure.set :as set]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.types.solve :as solve-types]))

(defn nogood-members
  "Every handle a nogood involves — its positive members (`:nogood`, forbidden to hold
  together) and its negated members (`:neg`, forbidden to be *absent* together, e.g. an
  at-least-one requirement).  `:neg` is optional and usually absent."
  [ng]
  (into (set (:nogood ng)) (:neg ng)))

(defn program
  "Build a solver Program for a set of `contested` handles and the `nogoods` among
  them, keeping only the nogoods with a contested member.  Contradiction members that
  are not contested are `fixed`: known-true background, assumed and never decided.
  `content` maps each contested handle to `{:sentence :context}`, which `content-key`
  orders by.

  `cardinalities` (optional) are the at-most-`k` / at-least-`k` bounds `solve-context`
  grounds from `asp/atMost` / `asp/atLeast`; their members are contested heads.

  `derivations` (optional) are a solve's ground normal rules, `[{:head id :pos #{id}
  :neg #{id}} …]`.  Every head one derives that is not contested is a `:derived` atom,
  neither an assumption nor fixed.  This arity also keeps a nogood over derived atoms
  alone and a hard nogood with no member, which no model satisfies."
  ([contested nogoods content] (program contested nogoods content []))
  ([contested nogoods content cardinalities]
   (let [contested (set contested)
         relevant  (filterv #(seq (set/intersection (nogood-members %) contested)) nogoods)
         fixed     (into #{} (comp (mapcat nogood-members) (remove contested)) relevant)]
     (solve-types/->Program contested fixed relevant (select-keys content contested) (vec cardinalities))))
  ([contested nogoods content cardinalities derivations]
   (let [contested (set contested)
         derived   (into #{} (comp (map :head) (remove contested)) derivations)
         atoms     (into contested derived)
         relevant  (filterv #(or (seq (set/intersection (nogood-members %) atoms))
                                 (and (:hard %) (empty? (nogood-members %))))
                            nogoods)
         fixed     (into #{} (comp (mapcat nogood-members) (remove atoms)) relevant)]
     (assoc (solve-types/->Program contested fixed relevant (select-keys content atoms)
                                   (vec cardinalities))
            :derived derived
            :derivations (vec derivations)))))

(defn content-key
  "A total order key on `program`'s contested assumptions, read off **what each asserts**:
  the sentence, then the context, then the handle for identical content.  The print vars
  are bound off, so an ambient `*print-length*` cannot elide the key and leave the order
  to arrival (docs/nmtms.md, \"1. Order independence\")."
  [program handle]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (pr-str [(get-in program [:content handle :sentence])
             (get-in program [:content handle :context])
             handle])))                              ; last resort: identical content

(def local-solver
  "A deterministic greedy `Solver`: walk the contradictions highest priority first, then
  by their members' `content-key`s, and satisfy each still-unsatisfied one by defeating
  its contested member with the greatest `content-key`.  A contradiction with no live
  contested member is reported violated.  It does not optimize globally, so two
  overlapping pairs can cost two defeats where the optimum spends one (docs/asp.md,
  \"The objective\")."
  (reify solve-types/Solver
    (solve [_ {:keys [assumptions contradictions] :as program}]
      (loop [defeated #{}
             violated []
             ;; the member keys are compared as a vector, not re-printed: a `pr-str` of
             ;; the list would elide under an ambient `*print-length*`
             ngs (nm/sort-by-content-key
                  (fn [ng]
                    [(- (:priority ng))
                     (vec (sort (map #(content-key program %)
                                     (concat (:nogood ng) (:neg ng)))))])
                  nm/compare-form
                  contradictions)]
        (if (empty? ngs)
          {:defeat defeated :violated violated}
          (let [{:keys [nogood neg] :as ng} (first ngs)
                live      (remove defeated nogood)
                present   (remove defeated neg)      ; `:neg` members still believed
                choosable (filter assumptions live)]
            (cond
              ;; satisfied once one member is out, not once one is left: a wider nogood
              ;; with one member defeated still has two live
              (< (count live) (count nogood)) (recur defeated violated (rest ngs))
              ;; the `:neg` half is an at-least-one, satisfied by any member still
              ;; believed; with every member defeated nothing can be chosen
              (and (seq neg) (seq present)) (recur defeated violated (rest ngs))
              (empty? choosable)  (recur defeated (conj violated ng) (rest ngs)) ; cannot satisfy
              :else (recur (conj defeated (last (sort-by #(content-key program %) choosable)))
                           violated (rest ngs)))))))))
