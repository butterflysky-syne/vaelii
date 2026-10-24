;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-algebra-test
  "The relation-algebra laws over every shipped algebra, and each calculus's vocabulary
  over its algebra (docs/qcn.md, on what the laws hold over RCC-8's table).  Associativity
  is not among them: `vaelii.impl.distance` composes weakly, exact per pair of classes."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.point :as pt]
            [vaelii.impl.relative :as rel]
            [vaelii.impl.space :as space]))

(def algebras
  "Every shipped algebra, by name."
  {:rcc8     space/rcc8-algebra
   :allen    iv/allen-algebra
   :cardinal dir/direction-algebra
   :relative rel/relative-algebra
   :distance dist/distance-algebra
   :point    pt/point-algebra})

(def calculi
  "Every shipped calculus, by name — the algebra plus the vocabulary over it."
  {:rcc8     space/rcc8
   :allen    iv/allen
   :cardinal dir/cardinal
   :relative rel/relative
   :distance dist/qualitative-distance
   :point    pt/instants})

(defn- offenders
  "At most five members of `xs` that fail `ok?`, so a law is one assertion per algebra."
  [ok? xs]
  (into [] (comp (remove ok?) (take 5)) xs))

(defn- base-pairs [universe]
  (for [a universe b universe] [a b]))

(defn- base-triples [universe]
  (for [a universe b universe c universe] [a b c]))

;; ---- the laws ------------------------------------------------------------

(deftest converse-is-a-total-involution-on-the-universe
  (doseq [[nm {:keys [universe converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders #(set/subset? (converse #{%}) universe) universe))
          "every relation's converse is a relation of the algebra")
      (is (= [] (offenders #(= 1 (count (converse #{%}))) universe))
          "a base relation's converse is a base relation, not a disjunction")
      (is (= [] (offenders #(= #{%} (converse (converse #{%}))) universe))
          "converse is its own inverse")
      (is (= universe (converse universe))
          "so the universe is its own converse"))))

(deftest composition-is-closed-and-never-empty
  (doseq [[nm {:keys [universe compose]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b]] (set/subset? (compose #{a} #{b}) universe))
                           (base-pairs universe)))
          "no cell names a relation outside the algebra")
      ;; jointly exhaustive: some relation always holds of the outer pair, so a cell that
      ;; composed to nothing would report a satisfiable network inconsistent
      (is (= [] (offenders (fn [[a b]] (seq (compose #{a} #{b})))
                           (base-pairs universe)))
          "no cell is empty"))))

(deftest the-identity-is-a-singleton-self-converse-and-two-sided
  (doseq [[nm {:keys [universe identity compose converse]}] algebras]
    (testing (name nm)
      (is (= 1 (count identity)) "the diagonal constraint is one relation")
      (is (set/subset? identity universe) "and one the algebra has")
      (is (= identity (converse identity)) "a thing stands to itself the same way round")
      (is (= [] (offenders #(and (= #{%} (compose identity #{%}))
                                 (= #{%} (compose #{%} identity)))
                           universe))
          "composing with the identity on either side changes nothing"))))

(deftest converse-reverses-composition
  (doseq [[nm {:keys [universe compose converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b]]
                             (= (converse (compose #{a} #{b}))
                                (compose (converse #{b}) (converse #{a}))))
                           (base-pairs universe)))
          "(a∘b)⌣ = b⌣∘a⌣ over every pair of base relations"))))

(deftest the-cycle-law-ties-the-three-operations-together
  (doseq [[nm {:keys [universe compose converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b c]]
                             (= (contains? (compose #{a} #{b}) c)
                                (boolean (seq (set/intersection
                                               (compose (converse #{a}) #{c}) #{b})))))
                           (base-triples universe)))
          "c ∈ a∘b ⟺ a⌣∘c meets b"))))

(deftest composition-and-converse-distribute-over-union
  ;; what the bitmask compilation assumes, over three sets rather than 2^k
  (doseq [[nm {:keys [universe identity compose converse]}] algebras]
    (testing (name nm)
      (let [union-of  (fn [f s] (into #{} (mapcat f) s))
            some-sets [universe identity (set/difference universe identity)]]
        (is (= [] (offenders #(= (converse %) (union-of (fn [r] (converse #{r})) %))
                             some-sets))
            "the converse of a set is the union of its members' converses")
        (is (= [] (offenders (fn [[s1 s2]]
                               (= (compose s1 s2)
                                  (union-of (fn [a] (union-of #(compose #{a} #{%}) s2)) s1)))
                             (for [s1 some-sets s2 some-sets] [s1 s2])))
            "and a composition of sets the union of the pairwise compositions")))))

;; ---- the vocabulary over the algebra -------------------------------------

(deftest every-denotation-is-a-subset-of-the-universe
  ;; a relation outside the universe encodes to nothing
  (doseq [[nm calc] calculi]
    (testing (name nm)
      (let [universe (:universe (:algebra calc))]
        (is (= [] (offenders #(set/subset? ((:denotation calc) %) universe)
                             (:predicates calc)))
            "no predicate denotes a relation outside the algebra")
        (is (= [] (offenders #(seq ((:denotation calc) %)) (:predicates calc)))
            "and none denotes nothing at all")))))

(deftest the-base-predicates-are-the-singletons-and-cover-the-universe
  (doseq [[nm calc] calculi]
    (testing (name nm)
      (let [universe   (:universe (:algebra calc))
            denotation (:denotation calc)
            singletons (filter #(= 1 (count (denotation %))) (:predicates calc))]
        (is (= universe (into #{} (mapcat denotation) singletons))
            "every base relation has a predicate of its own")
        (is (= (count universe) (count singletons))
            "and no two predicates name the same one")))))
