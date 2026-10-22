;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.absent-type-order-test
  "Order independence where a derivation reads the **absence** of a type.

  An argument constraint convicts a sentence when the argument's types have no path to
  the declared one, and `mintable-type?` declines a mint whose type an arity statement
  binds to another length.  Both read the KB as it stands, so each needs a way back for the order
  where the missing edge or membership arrives later: a dropped rule conclusion, a
  declined decontextualized copy and an unminted declaration are remembered and re-asked
  by `settle` (docs/exceptions.md, \"A refused firing is remembered as bindings\").  And a
  `forced_decontextualized_predicate` declaration moves the extent stored before it.

  Each test runs the same sentences in both orders on a fresh KB and compares what the
  KB holds, stored and believed.  `starter-in-any-order` is the same claim over the
  whole shipped ontology."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- held
  "What `kb` stores, as a multiset of printed `[sentence context]` pairs with the rule
  handle an `exceptWhen` meta names blanked — the one place content carries a handle,
  and handles are allocated in arrival order."
  [kb]
  (frequencies
   (for [h (p/sentex-ids (:records kb))
         :let [sx (p/get-sentex (:records kb) h)]]
     [(str/replace (pr-str (:sentence sx)) #"\(sentexHandle \d+\)" "(sentexHandle _)")
      (str (:context sx))
      (v/in? kb h)])))

(defn- in-both-orders
  "Run `steps` (a map of step name to a fn of the KB) in `first-steps` then the rest, and
  in the reverse, each on a fresh KB after `setup`; return `[reading-a reading-b]`, each
  `(observe kb)`."
  [setup steps order-a observe]
  (for [order [order-a (reverse order-a)]]
    (tu/with-neutral-kb [kb tu/fresh]
      (setup kb)
      (doseq [s order] ((steps s) kb))
      (observe kb))))

(defn- a-type [kb t ctx] (v/assert kb (list 'genl t 'thing) ctx {:strength :monotonic}))

(defn- a-binary [kb t] (v/assert kb (list 'binary_predicate t) 'CxUniverse {:strength :monotonic}))

(defn- unbind [kb t] (v/retract! kb (v/handle-of kb (list 'binary_predicate t) 'CxUniverse)))

(defn- a-context [kb ctx super] (v/assert kb (list 'genlCx ctx super) 'CxUniverse {:strength :monotonic}))

(tu/deftest-kb a-forced-declaration-arriving-last-rehomes-what-was-stored-before-it
  ;; The declaration forces the storage context of every `(P …)` asserted after it; one
  ;; asserted before it stayed where it was written, so which context held the fact —
  ;; and the entailments a fact there draws — was the order.
  (tu/with-terms [linkedTo Alpha Beta CxWorld]
    (let [readings (in-both-orders
                    #(a-context % CxWorld 'CxUniverse)
                    {:decl #(v/assert % (list 'forced_decontextualized_predicate linkedTo) 'CxUniverse)
                     :fact #(v/assert % (list linkedTo Alpha Beta) CxWorld)}
                    [:decl :fact]
                    (fn [kb] {:universe (some? (v/handle-of kb (list linkedTo Alpha Beta) 'CxUniverse))
                              :world    (some? (v/handle-of kb (list linkedTo Alpha Beta) CxWorld))
                              :held     (held kb)}))]
      (is (apply = readings) "both orders hold the same sentexes")
      (is (:universe (first readings)) "the fact lives in CxUniverse")
      (is (not (:world (first readings))) "and not where it was written"))))

(tu/deftest-kb a-conclusion-convicted-by-a-missing-edge-is-placed-once-the-edge-arrives
  ;; `(arg ownsPet 2 animal)` is written in CxTheory, above the rule's context, so there
  ;; it constrains without entailing.  Rex is a `poodleKind`, and until the edge
  ;; `(genl poodleKind animal)` arrives nothing reaches `animal` from there: the firing
  ;; is dropped.  Arriving first, the same edge lets it through — so a KB that drops it
  ;; for good believes less in one order than the other.
  (tu/with-terms [animal poodleKind petOf ownsPet Rex Ann CxTheory CxWorld]
    (let [readings (in-both-orders
                    (fn [kb]
                      (a-context kb CxTheory 'CxUniverse)
                      (a-context kb CxWorld CxTheory)
                      (a-type kb animal CxTheory)
                      (a-type kb poodleKind CxTheory)
                      (v/assert kb (list 'arg ownsPet 2 animal) CxTheory)
                      (v/assert kb (list 'set/forwardRule
                                         (list 'implies (list petOf '?x '?y) (list ownsPet '?y '?x)))
                                CxWorld))
                    {:edge #(v/assert % (list 'genl poodleKind animal) CxTheory)
                     :fact #(do (v/assert % (list poodleKind Rex) CxWorld)
                                (v/assert % (list petOf Rex Ann) CxWorld))}
                    [:edge :fact]
                    (fn [kb] {:owns (boolean (v/ask? kb (list ownsPet Ann Rex) CxWorld))
                              :held (held kb)}))]
      (is (:owns (first readings)) "the edge first: the conclusion is placed")
      (is (apply = readings) "and the edge last reaches the same KB"))))

(tu/deftest-kb a-declaration-whose-type-loses-its-other-arity-mints-then
  ;; `mintable-type?` reads the declared type's own arity.  The declaration and the fact
  ;; arriving while `(binary_predicate gadgetKind)` stands mint nothing and wait; the
  ;; settle after the binding leaves re-asks them.  Forced to the entailing reading, since
  ;; the mint is what it asks about.
  (tu/with-entailing
    (doseq [kind ['arg 'genlArg]]
      (testing (str kind)
        (tu/with-terms [gadgetKind usesTool Ann Widget widgetKind CxWorld]
          (let [arg?     (= 'arg kind)
                ;; `genlArg` types a position that names a kind, so its argument is a type
                used     (if arg? Widget widgetKind)
                decl     (list kind usesTool 2 gadgetKind)
                minted   (if arg? (list gadgetKind Widget) (list 'genl widgetKind gadgetKind))
                readings (in-both-orders
                          #(do (a-context % CxWorld 'CxUniverse) (a-binary % gadgetKind))
                          {:unbind #(unbind % gadgetKind)
                           :rest   #(do (v/assert % decl CxWorld)
                                        (v/assert % (list usesTool Ann used) CxWorld))}
                          [:unbind :rest]
                          (fn [kb] {:minted (some? (v/handle-of kb minted CxWorld))
                                    :held   (held kb)}))]
            (is (:minted (first readings)) "the binding gone first: the declaration mints")
            (is (apply = readings) "and the binding gone last reaches the same KB")))))))

;; ---- the rebuild after recover ---------------------------------------------------

(tu/deftest-kb a-rebuild-walks-no-declared-type-to-thing
  ;; twelve declarations over four types, one bound to two arguments: the rebuild asks
  ;; no type whether it reaches `thing`, and notes the bound type's three declarations
  ;; again after their entries are dropped
  (tu/with-entailing
    (tu/with-terms [toolKind partKind gadgetKind floatingKind CxWorld]
      (tu/with-neutral-kb [kb tu/fresh]
        (a-context kb CxWorld 'CxUniverse)
        (a-binary kb floatingKind)
        (let [types (vector toolKind partKind gadgetKind floatingKind)
              _     (doseq [i (range 12)]
                      (v/assert kb (list 'arg (tu/fresh-term :predicate 'usesKind) 1
                                         (types (mod i 4)))
                                CxWorld))
              noted (set (map first (special/mint-refusals kb)))
              walks (atom [])
              global tax/genl?-global]
          (doseq [h noted] (#'special/drop-pending! kb h :mint))
          (with-redefs [tax/genl?-global (fn [tx sub super]
                                           (when (= 'thing super) (swap! walks conj sub))
                                           (global tx sub super))]
            (special/rebuild-pending! kb))
          (is (= 3 (count noted)) "the bound type's declarations wait")
          (is (empty? @walks) (str "walks to thing: " (frequencies @walks)))
          (is (= noted (set (map first (special/mint-refusals kb))))
              "the rebuild notes them again"))))))

(tu/deftest-kb a-rebuild-asks-each-stating-context-once-whether-it-sees-the-universe
  ;; six facts of a decontextualized predicate over two contexts: the lift walk asks
  ;; `sees?` from each stating context once, not once per fact
  (tu/with-terms [liftedRel Alpha CxWorld CxOther]
    (tu/with-neutral-kb [kb tu/fresh]
      (a-context kb CxWorld 'CxUniverse)
      (a-context kb CxOther 'CxUniverse)
      (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse
                {:strength :monotonic})
      (doseq [i (range 6)]
        (v/assert kb (list liftedRel Alpha (tu/fresh-term :individual 'Beta))
                  (if (even? i) CxWorld CxOther)))
      (let [asks (atom [])
            sees tax/sees?]
        (with-redefs [tax/sees? (fn [tx k y]
                                  (when (and (= 'CxUniverse y) (#{CxWorld CxOther} k))
                                    (swap! asks conj k))
                                  (sees tx k y))]
          (special/rebuild-pending! kb))
        (is (= {CxWorld 1 CxOther 1} (frequencies @asks)))))))

;; ---- the settle's re-ask ---------------------------------------------------------

(defn- release-asks
  "How many waiting declarations `special/release-mint!` re-asks while `f` runs."
  [f]
  (let [n (atom 0) real special/release-mint!]
    (with-redefs [special/release-mint! (fn [& args] (swap! n inc) (apply real args))]
      (f))
    @n))

(tu/deftest-kb a-write-that-moves-no-waiting-type-s-length-re-asks-no-entry
  ;; four declarations wait on a type bound to two arguments.  A membership, a `genl`
  ;; edge between two other types and a rolled-back preview re-ask none of them; the
  ;; binding leaving re-asks each once and releases it, and the last entry to leave takes
  ;; the settled generations with it.
  (tu/with-entailing
    (tu/with-terms [orphan toolKind partKind qKind Widget Gear CxWorld]
      (tu/with-neutral-kb [kb tu/fresh]
        (a-context kb CxWorld 'CxUniverse)
        (a-type kb toolKind CxWorld)
        (a-binary kb orphan)
        (doseq [_ (range 4)]
          (v/assert kb (list 'arg (tu/fresh-term :predicate 'usesKind) 1 orphan) CxWorld))
        (let [fact  (release-asks #(v/assert kb (list toolKind Widget) CxWorld))
              edge  (release-asks #(v/assert kb (list 'genl partKind toolKind) CxWorld))
              prev  (release-asks #(v/preview kb {:add [[(list 'genl qKind 'thing) CxWorld]]}))
              after (release-asks #(v/assert kb (list toolKind Gear) CxWorld))]
          (is (= [0 0 0 0] [fact edge prev after]))
          (is (= 4 (count (special/mint-refusals kb))) "the declarations still wait")
          (is (= 4 (release-asks #(unbind kb orphan))) "the binding leaving re-asks each")
          (is (= [[] false]
                 [(special/mint-refusals kb)
                  (contains? @(reasoning/refused kb) ::special/mints-settled)])))))))

;; ---- the kind index -------------------------------------------------------------

(defn- kinds-by-walk
  "The kind index a walk of every entry in `kb`'s refusal record builds: per kind, the
  handles holding an entry of it, nil when none does."
  [kb]
  (let [m @(reasoning/refused kb)]
    (not-empty
     (reduce (fn [acc [k recs]]
               (reduce (fn [acc kind]
                         (if (and (set? recs) (some kind recs))
                           (update acc kind (fnil conj #{}) k)
                           acc))
                       acc
                       [:constraint :lift :mint]))
             {}
             (dissoc m :kinds)))))

(tu/deftest-kb the-kind-index-names-the-handles-a-walk-of-the-record-finds
  ;; A settle pass reads the constraint and mint entries off the kind index alone, so an
  ;; entry of a kind under a handle the index does not name is never re-asked.  Each
  ;; step records, releases or orphans one entry, and the index is compared with a walk
  ;; of the whole record after it.
  (tu/with-entailing
    (tu/with-terms [animal poodleKind petOf ownsPet Rex Ann gadgetKind usesTool Bob Widget
                    CxTheory CxWorld]
      (tu/with-neutral-kb [kb tu/fresh]
        (let [seen (volatile! [])
              step (fn [label]
                     (vswap! seen conj [label (:kinds @(reasoning/refused kb))
                                        (= (kinds-by-walk kb) (:kinds @(reasoning/refused kb)))]))
              rule (list 'set/forwardRule
                         (list 'implies (list petOf '?x '?y) (list ownsPet '?y '?x)))]
          (a-context kb CxTheory 'CxUniverse)
          (a-context kb CxWorld CxTheory)
          (a-type kb animal CxTheory)
          (a-type kb poodleKind CxTheory)
          (a-binary kb gadgetKind)
          (v/assert kb (list 'disjoint poodleKind animal) CxTheory)
          (v/assert kb (list 'arg ownsPet 2 animal) CxTheory)
          ;; the conviction under the constraint-only reading, the one that convicts a
          ;; symbol; the mint and the releases under the entailing one
          (let [rh (tu/without-entailing
                    (let [rh (v/assert kb rule CxWorld)]
                      (v/assert kb (list poodleKind Rex) CxWorld)
                      (v/assert kb (list petOf Rex Ann) CxWorld)
                      (step :conviction-recorded)
                      rh))]
            (v/assert kb (list usesTool Bob Widget) CxWorld)
            (let [dh (v/assert kb (list 'arg usesTool 2 gadgetKind) CxWorld)]
              (step :mint-recorded)
              (v/retract! kb rh)
              (step :rule-retracted)
              (unbind kb gadgetKind)
              (step :mint-released)
              (v/retract! kb dh)
              (step :declaration-retracted)))
          (let [[[_ k1] [_ k2] [_ k3] [_ k4]] @seen]
            (is (every? last @seen) (str "the kind index and the walk differ: " (pr-str @seen)))
            (is (= [#{:constraint} #{:constraint :mint} #{:mint} nil]
                   [(set (keys k1)) (set (keys k2)) (set (keys k3)) k4])
                "each step moved the kind it names")))))))

;; ---- the whole shipped ontology -----------------------------------------------

(defn- starter-entries
  "Every sentence the starter loads, as `[sentence context]`, in the shipped loader's
  order: the upper files into CxUniverse, then the middle contexts."
  []
  (concat (for [f (core-context/upper-files)    s (seed/read-sentences f "upper")]  [s 'CxUniverse])
          (for [c (seed/layer-contexts "middle") s (seed/read-sentences c "middle")] [s c])))

(defn- load-shuffled!
  "The starter's sentences in the order `seed` shuffles them to, through the text
  loader, then the starter's closing `unary_predicate` batch."
  [kb seed]
  (let [l (java.util.ArrayList. ^java.util.Collection (vec (starter-entries)))]
    (java.util.Collections/shuffle l (java.util.Random. (long seed)))
    (v/with-deferred-settle kb
      (text/load-entries! (fn [s c o] (v/assert kb s c (or o {})))
                          (fn [s c] (v/assert-inert kb s c))
                          (vec l)))
    (v/with-deferred-settle kb
      (doseq [t (nm/by-print-key (v/specs kb 'thing))]
        (v/assert kb (list 'unary_predicate t) 'CxUniverse)))
    kb))

(defn- held-after
  "`(held kb)` after `load!` on a cleared KB of its own, cleared again after."
  [load!]
  (let [kb (tu/isolated-fresh)]
    (try (held (load! kb)) (finally (tu/clear-kb! kb)))))

(defn- starter-in-orders
  "Each shuffled order in `seeds` against the shipped one.  The shipped reading is the
  restored starter dump — `starter/load-into`'s KB, which `starter_copy_test` tests — so
  a run pays for the shuffled loads alone."
  [seeds]
  (let [shipped (held-after tu/load-starter!)]
    (doseq [s seeds]
      (let [shuffled (held-after #(load-shuffled! % s))]
        (is (= shipped shuffled)
            (str "seed " s ": held only by the shipped order "
                 (pr-str (take 5 (remove (set (keys shuffled)) (keys shipped))))
                 ", only by the shuffled one "
                 (pr-str (take 5 (remove (set (keys shipped)) (keys shuffled))))))))))

(deftest starter-in-any-order
  ;; one shuffled order at :default; `starter-in-many-orders` runs twenty
  (starter-in-orders [7]))

(deftest ^:slow starter-in-many-orders
  (starter-in-orders (range 100 120)))
