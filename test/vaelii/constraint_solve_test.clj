;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-solve-test
  "Constraint rules (`set/hardConstraint` / `set/softConstraint`) and `do/label`'s `:one`
  and `:sat` modes: a nogood over two different individuals, on graph 3-colouring and on a
  traveling-salesman tour.  The solving tests are guarded on `asp?`; the wrapper and record
  tests run without a backend."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. the constraint wrapper marks the record, and never chains --------

(deftest a-constraint-rule-is-marked-and-inference-inert
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [colored benchEdge]
      (let [body (list 'implies
                       (list 'and (list benchEdge '?x '?y)
                             (list colored '?x '?k) (list colored '?y '?k))
                       (list 'monochrome '?x '?y))
            hard (v/assert kb (list 'set/hardConstraint body) 'CxUniverse)
            soft (v/assert kb (list 'set/softConstraint body) 'CxUniverse)
            bare (v/assert kb body 'CxUniverse)]
        (testing "the wrapper is part of identity: hard, soft, and bare are three sentexes"
          (is (not= hard soft))
          (is (not= hard bare))
          (is (not= soft bare)))
        (testing "constraint-of reads the class off the record"
          (is (= :hard (rules/constraint-of (sentex-of kb hard))))
          (is (= :soft (rules/constraint-of (sentex-of kb soft))))
          (is (nil? (rules/constraint-of (sentex-of kb bare)))))
        (testing "a constraint rule forward- and backward-chains for nobody"
          (is (not (rules/forward-sentex? (sentex-of kb hard))))
          (is (not (rules/backward-sentex? (sentex-of kb hard))))
          (is (rules/backward-sentex? (sentex-of kb bare))
              "while a bare rule chains — backward, the default"))
        (testing "and re-asserting the same hard constraint is idempotent"
          (is (= hard (v/assert kb (list 'set/hardConstraint body) 'CxUniverse))))))))

(deftest a-constraint-rule-derives-no-marker
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [colored benchEdge A B]
      (v/assert kb (list 'set/hardConstraint
                         (list 'implies
                               (list 'and (list benchEdge '?x '?y)
                                     (list colored '?x '?k) (list colored '?y '?k))
                               (list 'monochrome '?x '?y)))
                'CxUniverse)
      ;; even given a monochrome edge as plain facts, nothing derives the marker
      (v/assert kb (list benchEdge A B) 'CxUniverse)
      (v/assert kb (list colored A 'red) 'CxUniverse)
      (v/assert kb (list colored B 'red) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list 'monochrome A B) 'CxUniverse))))))

;; ---- 2. hard 3-coloring end to end via do/label … :one -------------------

(defn- install-3coloring!
  "The choice + functional + hard-adjacency program over `nodes` and `edges` in `ctx`."
  [kb ctx colored nodes edges]
  (doseq [k '[k1 k2 k3]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'bench_node '?x) (list colored '?x k)))
              ctx))
  (v/assert kb (list 'functional colored) ctx {:strength :monotonic})
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'benchEdge '?x '?y)
                                 (list colored '?x '?k) (list colored '?y '?k))
                           (list 'monochrome '?x '?y)))
            ctx)
  (doseq [n nodes] (v/assert kb (list 'bench_node n) ctx {:strength :monotonic}))
  (doseq [[a b] edges] (v/assert kb (list 'benchEdge a b) ctx {:strength :monotonic})))

(defn- coloring-of
  "node -> colour, read from a `:one` labeling's chosen-true `(colored node k)` heads."
  [labeling]
  (into {} (map (fn [s] [(nth s 1) (nth s 2)])) (:true labeling)))

(deftest hard-constraint-3-colors-a-triangle
  ;; A triangle is 3-colorable and needs all three colours: the tightest small witness
  ;; that the adjacency constraint over *different* nodes is honored.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxTri colored
                            '[N1 N2 N3] '[[N1 N2] [N2 N3] [N1 N3]])
        (let [r        (v/assert kb (list 'do/label 'CxTri 'CxTriPlan :one) 'CxTri)
              labeling (first (:labelings r))
              coloring (coloring-of labeling)]
          (testing "one labeling, computed and returned but not persisted"
            (is (= 1 (:count r)))
            (is (nil? (:context labeling)))
            (is (not (contains? (set (v/contexts kb)) 'CxTriPlan1))))
          (testing "every node gets exactly one colour"
            (is (= #{'N1 'N2 'N3} (set (keys coloring))))
            (is (= 3 (count (:true labeling))) "one chosen colour per node")
            (is (= 6 (count (:false labeling)))
                "the other two colours per node are chosen-false (3 nodes × 2)"))
          (testing "no edge is monochrome — a proper colouring"
            (doseq [[a b] '[[N1 N2] [N2 N3] [N1 N3]]]
              (is (not= (coloring a) (coloring b)) (str a "-" b))))
          (testing "a triangle exhausts all three colours"
            (is (= 3 (count (set (vals coloring))))))
          (testing "base belief is untouched — no colour is believed, nothing contradicts"
            (is (empty? (v/sentexes-matching kb (list colored 'N1 'k1) 'CxTri)))
            (is (zero? (count (v/contradictions kb))))))))))

(deftest hard-constraint-3-colors-a-path
  ;; A 4-node path, 3-colorable with a colour to spare — checks the join grounds the
  ;; right per-edge nogoods when nodes share endpoints.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxPath colored
                            '[P1 P2 P3 P4] '[[P1 P2] [P2 P3] [P3 P4]])
        (let [r        (v/assert kb (list 'do/label 'CxPath 'CxPathPlan :one) 'CxPath)
              coloring (coloring-of (first (:labelings r)))]
          (is (= 1 (:count r)))
          (is (= #{'P1 'P2 'P3 'P4} (set (keys coloring))) "all four nodes coloured")
          (doseq [[a b] '[[P1 P2] [P2 P3] [P3 P4]]]
            (is (not= (coloring a) (coloring b)) (str a "-" b))))))))

(deftest a-clique-of-four-is-not-3-colorable
  ;; K4 has no proper 3-colouring; with no hard at-least-one the program is satisfiable,
  ;; and the keep-belief optimum leaves a node uncoloured
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxK4 colored
                            '[Q1 Q2 Q3 Q4]
                            '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]])
        (let [r        (v/assert kb (list 'do/label 'CxK4 'CxK4Plan :one) 'CxK4)
              coloring (coloring-of (first (:labelings r)))]
          (testing "no proper total 3-colouring: some node is left uncoloured"
            (is (< (count coloring) 4)))
          (testing "and whatever it did colour has no monochrome edge among the coloured"
            (doseq [[a b] '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]]]
              (when (and (coloring a) (coloring b))
                (is (not= (coloring a) (coloring b)) (str a "-" b))))))))))

(deftest three-colors-the-australia-map
  ;; The textbook CSP: the six states of mainland Australia + Tasmania.  Its triangles
  ;; (Wa-Nt-Sa, Sa-Nsw-V, …) force all three colours, and Tasmania has no land border —
  ;; the keep-belief `:one` objective colours it anyway, since a coloured node keeps a
  ;; choice while an uncoloured one defeats all three.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (let [regions '[Wa Nt Sa Q Nsw V T]
              borders '[[Wa Nt] [Wa Sa] [Nt Sa] [Nt Q] [Sa Q]
                        [Sa Nsw] [Sa V] [Q Nsw] [Nsw V]]]
          (install-3coloring! kb 'CxAustralia colored regions borders)
          (let [r        (v/assert kb (list 'do/label 'CxAustralia 'CxAustraliaPlan :one) 'CxAustralia)
                coloring (coloring-of (first (:labelings r)))]
            (testing "all seven regions coloured, Tasmania included"
              (is (= (set regions) (set (keys coloring))))
              (is (contains? coloring 'T) "an isolated region is still coloured"))
            (testing "no shared border is monochrome — a proper colouring"
              (doseq [[a b] borders]
                (is (not= (coloring a) (coloring b)) (str a "-" b))))
            (testing "the map needs all three colours"
              (is (= 3 (count (set (vals coloring))))))))))))

;; ---- 2b. all-hard 3-coloring (at-least-one via negated choice literals) ---

(defn- install-allhard-3coloring!
  "The bench's all-hard recipe: colour choice per node, hard at-most-one, hard
  at-least-one (a negated-choice constraint), hard no-monochrome-edge."
  [kb ctx colored nodes edges]
  (doseq [k '[k1 k2 k3]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'bench_node '?x) (list colored '?x k)))
              ctx))
  (doseq [[ka kc] '[[k1 k2] [k1 k3] [k2 k3]]]
    (v/assert kb (list 'set/hardConstraint
                       (list 'implies (list 'and (list colored '?x ka) (list colored '?x kc))
                             (list 'double_colored '?x)))
              ctx))
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'bench_node '?x)
                                 (list 'not (list colored '?x 'k1))
                                 (list 'not (list colored '?x 'k2))
                                 (list 'not (list colored '?x 'k3)))
                           (list 'uncolored '?x)))
            ctx)
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'benchEdge '?x '?y)
                                 (list colored '?x '?k) (list colored '?y '?k))
                           (list 'monochrome '?x '?y)))
            ctx)
  (doseq [n nodes] (v/assert kb (list 'bench_node n) ctx {:strength :monotonic}))
  (doseq [[a b] edges] (v/assert kb (list 'benchEdge a b) ctx {:strength :monotonic})))

(deftest all-hard-colors-every-node-including-isolated
  ;; The exact bench encoding at unit scale, solved in **:sat** mode: the hard
  ;; at-least-one (a negated-choice `:- not colored(x,k1..k3)` constraint) forces a colour
  ;; on EVERY node — even one with no edges — so the solve is plain satisfaction with no
  ;; keep-belief objective, and still every node is coloured exactly once.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        ;; a triangle plus a totally isolated node Iso (no edges)
        (install-allhard-3coloring! kb 'CxAllHard colored
                                    '[N1 N2 N3 Iso] '[[N1 N2] [N2 N3] [N1 N3]])
        (let [r        (v/assert kb (list 'do/label 'CxAllHard 'CxAllHardPlan :sat) 'CxAllHard)
              coloring (coloring-of (first (:labelings r)))]
          (testing ":sat returns one labeling, persists nothing"
            (is (= 1 (:count r)))
            (is (nil? (:context (first (:labelings r))))))
          (testing "every node coloured exactly once, isolated node included"
            (is (= #{'N1 'N2 'N3 'Iso} (set (keys coloring)))))
          (testing "the triangle is properly coloured"
            (doseq [[a b] '[[N1 N2] [N2 N3] [N1 N3]]]
              (is (not= (coloring a) (coloring b)) (str a "-" b)))
            (is (= 3 (count (set (map coloring '[N1 N2 N3])))))))))))

(deftest a-negated-choice-literal-binds-its-own-variables
  ;; `?k` is bound by the negated literal alone.  `functional` makes two colours a soft
  ;; clash, so without the hard constraint there are two optima and with it one (both).
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored cand Item]
        (doseq [k '[k1 k2]]
          (v/assert kb (list 'set/assumptionRule
                             (list 'implies (list cand '?c) (list colored '?c k)))
                    'CxNegJoin))
        (v/assert kb (list 'functional colored) 'CxNegJoin)
        (v/assert kb (list cand Item) 'CxNegJoin {:strength :monotonic})
        (testing "without the at-least-one: two optima, one colour apiece"
          (is (= 2 (:count (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :all)
                                     'CxNegJoin)))))
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'not (list colored '?x '?k))
                                 (list 'mustColor '?x '?k)))
                  'CxNegJoin)
        (testing "with it: no colour may be absent, so the one legal world keeps both"
          (let [r (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :all) 'CxNegJoin)]
            (is (= 1 (:count r)))
            (is (empty? (:false (first (:labelings r)))))
            (is (= 2 (count (:true (first (:labelings r))))))))
        (testing "and :sat, with no keep-belief objective pushing the atoms true, agrees"
          (let [l (first (:labelings (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :sat)
                                               'CxNegJoin)))]
            (is (empty? (:false l)) "the first model found still satisfies the constraint")))))))

(deftest an-unsatisfiable-program-reports-no-labeling-rather-than-an-empty-one
  ;; K4 under the all-hard encoding admits no model, so `:one` / `:sat` report
  ;; `:unsatisfiable` and `:all` enumerates nothing
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-allhard-3coloring! kb 'CxUnsat colored
                                    '[Q1 Q2 Q3 Q4]
                                    '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]])
        (doseq [mode [:one :sat]]
          (let [r (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan mode) 'CxUnsat)]
            (testing (str mode " reports no world, and says why")
              (is (zero? (:count r)))
              (is (= :unsatisfiable (:reason r)))
              (is (empty? (:labelings r))))))
        (testing ":all agrees, having enumerated nothing"
          (is (zero? (:count (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan :all) 'CxUnsat)))))
        (testing "and the menu of choices is still reported — grounding did happen"
          (is (= 12 (count (:choices (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan :one)
                                               'CxUnsat))))
              "4 nodes × 3 colours"))))))

;; ---- 3. phase timings ride the :one result -------------------------------

(deftest one-mode-carries-phase-timings
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxUniverse colored '[T1 T2] '[[T1 T2]])
        (let [r (v/assert kb (list 'do/label 'CxUniverse 'CxTimePlan :one) 'CxUniverse)]
          (is (every? number? [(:ground-ms r) (:translate-ms r) (:solve-ms r)])
              "grounding / translate / solve are timed separately for a profiling caller"))))))

;; ---- traveling salesman: a permutation under hard constraints -------------
;; One tour position per city (`tourStop`), at most one city per position, at least one
;; position per city, and no step between two cities with no road (`notRoad` joined
;; against two consecutive positions).  With as many cities as positions the choices are
;; a bijection, so one `:sat` solve returns a Hamiltonian tour or reports none.
;; Five cities at five cyclic positions; roads are unordered pairs `#{a b}`.

(def ^:private cities    '[A B C D E])
(def ^:private positions '[P1 P2 P3 P4 P5])

;; A road graph that admits several Hamiltonian tours (the 5-cycle plus two chords).
(def ^:private roads
  #{#{'A 'B} #{'B 'C} #{'C 'D} #{'D 'E} #{'A 'E}   ; the outer 5-cycle
    #{'A 'C} #{'B 'D}})                             ; two chords → more than one tour

;; A 5-vertex path: a Hamiltonian *path* but no Hamiltonian *cycle* (no edge closes it).
(def ^:private path-roads
  #{#{'A 'B} #{'B 'C} #{'C 'D} #{'D 'E}})

;; ---- installing the program ----------------------------------------------

(defn- unordered-pairs [xs]
  (let [v (vec xs)]
    (for [i (range (count v)), j (range (inc i) (count v))] #{(v i) (v j)})))

(defn- cyclic-steps
  "Consecutive (Pa Pb) position pairs around the tour, wrapping the last back to the
  first — the slots the tour steps between."
  [positions]
  (map vector positions (concat (rest positions) [(first positions)])))

(defn- install-tsp!
  "The choice + permutation + no-illegal-step program over `cities` at `positions`
  (in cyclic order) for a `roads` graph, all in `ctx`."
  [kb ctx cities positions roads]
  (doseq [c cities] (v/assert kb (list 'city c) ctx {:strength :monotonic}))
  (doseq [p positions] (v/assert kb (list 'position p) ctx {:strength :monotonic}))
  (doseq [[a b] (cyclic-steps positions)]
    (v/assert kb (list 'nextPos a b) ctx {:strength :monotonic}))
  ;; the road complement, both directions — a step between them is forbidden
  (let [rset (set roads)]
    (doseq [pr (unordered-pairs cities)
            :when (not (rset pr))
            :let [[a b] (vec pr)]]
      (v/assert kb (list 'notRoad a b) ctx {:strength :monotonic})
      (v/assert kb (list 'notRoad b a) ctx {:strength :monotonic})))
  ;; choice: a tour position for each city (grounds |positions| × |cities| heads)
  (v/assert kb (list 'set/assumptionRule
                     (list 'implies (list 'and (list 'position '?p) (list 'city '?c))
                           (list 'tourStop '?p '?c)))
            ctx)
  ;; hard at-most-one city per position — one constraint per fixed city pair
  (doseq [pr (unordered-pairs cities) :let [[ca cb] (vec pr)]]
    (v/assert kb (list 'set/hardConstraint
                       (list 'implies (list 'and (list 'tourStop '?p ca) (list 'tourStop '?p cb))
                             (list 'two_cities_at '?p)))
              ctx))
  ;; hard at-least-one position per city — a negated-choice constraint over all positions
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (apply list 'and (list 'city '?c)
                                  (map (fn [p] (list 'not (list 'tourStop p '?c))) positions))
                           (list 'unplaced '?c)))
            ctx)
  ;; hard no-illegal-step — consecutive tour slots must hold cities joined by a road
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'nextPos '?pa '?pb) (list 'notRoad '?x '?y)
                                 (list 'tourStop '?pa '?x) (list 'tourStop '?pb '?y))
                           (list 'badStep '?x '?y)))
            ctx))

(defn- tour-of
  "position -> city, read from a `:sat` labeling's chosen-true `(tourStop pos city)` heads."
  [labeling]
  (into {} (map (fn [s] [(nth s 1) (nth s 2)])) (:true labeling)))

;; ---- a graph with a tour -------------------------------------------------

(deftest finds-a-hamiltonian-tour
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-tsp! kb 'CxTsp cities positions roads)
      (let [r    (v/assert kb (list 'do/label 'CxTsp 'CxTspPlan :sat) 'CxTsp)
            lab  (first (:labelings r))
            tour (tour-of lab)]
        (testing ":sat returns one labeling and persists nothing"
          (is (= 1 (:count r)))
          (is (nil? (:context lab)))
          (is (not (contains? (set (v/contexts kb)) 'CxTsp1))))
        (testing "the tour is a permutation: each position once, each city once"
          (is (= (set positions) (set (keys tour))))
          (is (= (set cities) (set (vals tour))) "every city visited exactly once")
          (is (= (count cities) (count (:true lab)))))
        (testing "every consecutive step of the tour follows a road"
          (doseq [[pa pb] (cyclic-steps positions)]
            (is (contains? roads #{(tour pa) (tour pb)})
                (str (tour pa) " -> " (tour pb) " must be a road"))))
        (testing "base belief is untouched — no tour position is believed"
          (is (empty? (v/sentexes-matching kb (list 'tourStop 'P1 'A) 'CxTsp)))
          (is (zero? (count (v/contradictions kb)))))))))

;; ---- a graph with no tour ------------------------------------------------

(deftest a-path-graph-has-no-tour
  ;; a path has no Hamiltonian cycle, so the program is unsatisfiable and no labeling
  ;; places a city
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-tsp! kb 'CxNoTour cities positions path-roads)
      (let [r    (v/assert kb (list 'do/label 'CxNoTour 'CxNoTourPlan :sat) 'CxNoTour)
            tour (tour-of (first (:labelings r)))]
        (testing "no full permutation tour exists, and the all-hard UNSAT keeps nothing"
          (is (< (count tour) (count cities)))
          (is (empty? tour)))))))
