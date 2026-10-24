;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-mask-test
  "The compiled bitmask tables against the algebra's own set-valued `:compose` and
  `:converse`: exhaustively where the relation count allows, over a seeded sample where it
  does not, and over a synthetic algebra wide enough to take the sparse table."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.qcn :as qcn]
            [vaelii.qcn-algebra-test :refer [algebras]])
  (:import [vaelii.impl.types.qcn IRelationOps]))

(def ^:private compile-algebra #'qcn/compile-algebra)

(defn- composed
  "The compiled composition of two masks."
  [compiled ^long m1 ^long m2]
  (.compose ^IRelationOps (:ops compiled) m1 m2))

(defn- conversed
  "The compiled converse of a mask."
  [compiled ^long m]
  (.converse ^IRelationOps (:ops compiled) m))

(defn- masks
  "Every mask of a `k`-relation algebra."
  [k]
  (range (bit-shift-left 1 k)))

(defn- sample-masks
  "`n` masks drawn from a `k`-relation algebra under `seed`."
  [k n seed]
  (let [rnd (java.util.Random. seed)
        hi  (bit-shift-left 1 k)]
    (repeatedly n #(.nextInt rnd hi))))

;; ---- the round trip ------------------------------------------------------

(deftest every-mask-decodes-to-the-set-that-encodes-to-it
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [encode decode universe identity]} (compile-algebra algebra)
            k (count (:universe algebra))]
        (is (= (:universe algebra) (decode universe))
            "the universe mask decodes to the algebra's universe")
        (is (= (:identity algebra) (decode identity))
            "the identity mask decodes to the algebra's identity")
        (is (= #{} (decode 0)) "the empty mask is the empty constraint")
        (doseq [m (masks k)]
          (is (= m (encode (decode m)))
              (str "mask " m " round-trips through its relation set")))))))

;; ---- the tables ----------------------------------------------------------

(deftest converse-agrees-with-the-algebra-on-every-constraint
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [decode] :as compiled} (compile-algebra algebra)
            set-converse (:converse algebra)
            k (count (:universe algebra))]
        (doseq [m (masks k)]
          (let [s (decode m)]
            (is (= (set-converse s) (decode (conversed compiled m)))
                (str "converse of " s))))))))

(deftest composition-agrees-with-the-algebra-on-every-pair-of-base-relations
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [encode decode] :as compiled} (compile-algebra algebra)
            set-compose (:compose algebra)]
        (doseq [a (:universe algebra)
                b (:universe algebra)]
          (is (= (set-compose #{a} #{b})
                 (decode (composed compiled (encode #{a}) (encode #{b}))))
              (str "compose " a " " b)))))))

(deftest composition-agrees-with-the-algebra-on-whole-constraints
  (doseq [[nm algebra] algebras]
    (testing (name nm)
      (let [{:keys [decode] :as compiled} (compile-algebra algebra)
            set-compose (:compose algebra)
            k    (count (:universe algebra))
            ;; exhaustive where 2^k squared is small (k <= 7), else a seeded sample
            pairs (if (<= k 7)
                    (for [a (masks k) b (masks k)] [a b])
                    (map vector (sample-masks k 4000 42) (sample-masks k 4000 4242)))]
        (doseq [[a b] pairs]
          (let [sa (decode a) sb (decode b)]
            (is (= (set-compose sa sb) (decode (composed compiled a b)))
                (str "compose " sa " " sb))))))))

;; ---- the two table strategies --------------------------------------------

(deftest the-two-numbers-that-bound-this-layer-are-the-documented-ones
  ;; docs/qcn.md, "Two numbers bound this layer, and neither is a cache"
  (is (= 62 @#'qcn/max-base-relations)
      "a constraint is the bits of a long, and 62 is what one holds")
  (is (= (bit-shift-left 1 18) @#'qcn/dense-table-limit)
      "the whole-mask composition table is built at or under this many entries"))

(deftest every-shipped-algebra-takes-the-dense-table
  (testing "the whole-mask table is affordable for all six, Allen's thirteen included"
    (doseq [[nm algebra] algebras]
      (let [k (count (:universe algebra))]
        (is (<= (* k (bit-shift-left 1 k)) (bit-shift-left 1 18))
            (str (name nm) " has " k " base relations, whose whole-mask table is "
                 (* k (bit-shift-left 1 k)) " entries"))))))

(def ^:private wide-relations
  "Sixteen base relations — enough that the whole-mask table (16 × 65536 entries) is over
  the limit, so a compiled algebra of them takes the base-table loop instead."
  (vec (map #(keyword (str "r" %)) (range 16))))

(def ^:private wide-base
  "A seeded composition table over them, not a sound algebra: the compilation reproduces
  the union over base pairs whatever those compose to."
  (let [rnd (java.util.Random. 7)]
    (into {} (for [a wide-relations]
               [a (into {} (for [b wide-relations]
                             [b (into #{} (remove nil?)
                                      (map (fn [r] (when (.nextBoolean rnd) r))
                                           wide-relations))]))]))))

(def ^:private wide-converse
  "Its converse: the relations paired off end to end, a permutation."
  (into {} (map-indexed (fn [i r] [r (nth wide-relations (- 15 i))])) wide-relations))

(def ^:private wide-algebra
  {:universe (set wide-relations)
   :identity #{(first wide-relations)}
   :compose  (fn [s1 s2]
               (into #{} (mapcat (fn [a] (mapcat #(get-in wide-base [a %]) s2))) s1))
   :converse (fn [s] (into #{} (map wide-converse) s))})

(deftest a-wide-algebra-falls-back-to-the-base-table-and-still-agrees
  (testing "sixteen relations is past the dense limit"
    (is (> (* 16 (bit-shift-left 1 16)) (bit-shift-left 1 18))))
  (let [{:keys [decode] :as compiled} (compile-algebra wide-algebra)
        set-compose  (:compose wide-algebra)
        set-converse (:converse wide-algebra)]
    (testing "converse over a deterministic sample"
      (doseq [m (sample-masks 16 2000 11)]
        (is (= (set-converse (decode m)) (decode (conversed compiled m))))))
    (testing "composition over a deterministic sample"
      (doseq [[a b] (map vector (sample-masks 16 3000 13) (sample-masks 16 3000 17))]
        (is (= (set-compose (decode a) (decode b))
               (decode (composed compiled a b))))))))

(deftest an-algebra-wider-than-a-mask-is-refused-rather-than-truncated
  (let [too-many (into #{} (map #(keyword (str "r" %))) (range 70))]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"base relations"
         (compile-algebra {:universe too-many
                           :identity #{:r0}
                           :compose  (fn [_ _] too-many)
                           :converse identity})))))
