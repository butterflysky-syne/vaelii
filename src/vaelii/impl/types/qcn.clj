;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.qcn
  "The two relation-algebra operations over masks, as a held namespace
  (`vaelii.impl.types.prover` states what that means): the `IRelationOps` interface and its
  dense and sparse implementations, which `vaelii.impl.qcn` compiles an algebra into.
  The implementations are primitive loops over `long[]` tables and call no vaelii
  namespace, so their methods stay inline.")

;; Primitive rather than a pair of closures: docs/defenses.md, "Composition runs through
;; `IRelationOps`; the triple walk is a closure".
(definterface IRelationOps
  (^long compose [^long m1 ^long m2])
  (^long converse [^long m]))

(deftype DenseOps [^longs comp-tbl ^longs conv-tbl ^long size]
  IRelationOps
  ;; `comp-tbl` row i: relation i composed with every mask
  (compose [_ m1 m2]
    (loop [a m1, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a))
                 (bit-or acc (aget comp-tbl (+ (* i size) m2))))))))
  (converse [_ m] (aget conv-tbl m)))

(defn- union-row
  "The union of `base[i][j]` over the relations set in `m`: one row of the base table,
  masked — the composition of a single relation with a whole constraint."
  ^long [^longs base ^long k ^long i ^long m]
  (loop [b m, acc 0]
    (if (zero? b)
      acc
      (let [j (Long/numberOfTrailingZeros b)]
        (recur (bit-and b (dec b))
               (bit-or acc (aget base (+ (* i k) j))))))))

(deftype SparseOps [^longs comp-base ^longs conv-base ^long k]
  IRelationOps
  ;; an algebra past the dense-table limit: the same unions, one base pair at a time
  (compose [_ m1 m2]
    (loop [a m1, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a))
                 (bit-or acc (union-row comp-base k i m2)))))))
  (converse [_ m]
    (loop [a m, acc 0]
      (if (zero? a)
        acc
        (let [i (Long/numberOfTrailingZeros a)]
          (recur (bit-and a (dec a)) (bit-or acc (aget conv-base i))))))))
