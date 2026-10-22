;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.argument
  "The argument family: a stored fact whose argument fails a declared argument type, and a
  stored rule whose variable no term can fill, read as `assert` reads them
  (`checks/argument-conviction`), are held in the `:out` forced set.  This namespace
  keeps the held sentexes and the queue of what can move a verdict; the settle drains the
  queue (`checks/refresh-argument-holds!`).  See docs/argtypes.md, \"An argument that
  fails its declared type is held inert\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the held facts and the queue ---------------------------------------------
;;
;; `::held` is `{h functor}`, the stored sentexes the family holds in `:out`, with a nil
;; functor for a rule.  A write queues what can move a verdict: an argument declaration
;; stored or removed queues `[predicate context]` under `::decls`, a membership `(T x)`
;; stored or removed queues `x` under `::terms`, and under `::kinds` as well when `T` is
;; `type_relation_predicate`, which constrains a rule's variables at every position of
;; `x`, and a definition `(defnSufficient T C)`, `(defnNecessary T C)` or
;; `(defnIff T C)` stored, removed or relabelled queues `T` under `::defns`, since it can
;; decide a value under a type at or below or above `T` (`provers/value-definition`).  `::read-under` holds the taxonomy generations the last drain read
;; (`special/conviction-generations` with the `genlCx` generation), and `::owed` marks a
;; recover, after which the first drain reads every declaration whole.  `::adopt` marks an
;; installed image that carries no `::read-under`: the first drain takes the generations as read and
;; reads only what the queue names (`installed!`).

(def declaration-functors
  "The argument declarations, each naming the predicate it constrains at argument 1
  (`predicates/:argument-constraint`)."
  (predicates/family :argument-constraint))

(defn- declaration-of
  "`[P context]` for a stored fact `sx` declaring an argument constraint of `P`, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (contains? declaration-functors (first s)))
      (let [p (second s)]
        (when (and (symbol? p) (not (sx/variable? p)))
          [p (:context sx)])))))

(defn- member-of
  "The term `x` of a stored fact `sx` whose sentence is the membership `(T x)` of a symbol,
  else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 2 (count s)))
      (let [[t x] s]
        (when (and (symbol? t) (not= 'not t) (not (sx/variable? t))
                   (symbol? x) (not (sx/variable? x)))
          x)))))

(defn- kind-of
  "The predicate `P` of a stored fact `sx` whose sentence is `(type_relation_predicate P)`,
  else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'type_relation_predicate (first s)))
      (member-of sx))))

(defn- defined-of
  "The type `T` a stored definition `sx`, `(defnSufficient T C)`, `(defnNecessary T C)` or
  `(defnIff T C)`, states a condition of, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (sx/defn-sentence? s))
      (let [t (second s)]
        (when (and (symbol? t) (not (sx/variable? t))) t)))))

(defn held?
  "Is the stored sentex at `h` held for an argument conviction?"
  [kb h]
  (contains? (::held @(reasoning/nogood-candidates kb)) h))

(defn held
  "`{h functor}` of every sentex the family holds."
  [kb]
  (::held @(reasoning/nogood-candidates kb) {}))

(defn set-held!
  "Record the sentex at `h`, of functor `f` (nil for a rule), as held (`on?`) or not."
  [kb h f on?]
  (swap! (reasoning/nogood-candidates kb)
         #(if on? (assoc-in % [::held h] f) (update % ::held dissoc h))))

(defn note!
  "Queue what the fact `sx` stored or removed (`stored?`) can move: a declaration's
  predicate and context, a membership's term, a definition's type.  A removed fact leaves
  `::held`."
  [kb sx stored?]
  (let [d (declaration-of sx)
        x (when-not d (member-of sx))
        k (when x (kind-of sx))
        t (when-not (or d x) (defined-of sx))]
    (when (or d x t (and (not stored?) (contains? (::held @(reasoning/nogood-candidates kb)) (:id sx))))
      (swap! (reasoning/nogood-candidates kb)
             #(cond-> %
                d                (update ::decls (fnil conj #{}) d)
                x                (update ::terms (fnil conj #{}) x)
                k                (update ::kinds (fnil conj #{}) k)
                t                (update ::defns (fnil conj #{}) t)
                (not stored?)    (update ::held dissoc (:id sx)))))))

(defn note-relabelled!
  "Queue the declarations, memberships and definitions among the stored facts `sxs` whose
  label moved."
  [kb sxs]
  (let [ds (into #{} (keep declaration-of) sxs)
        xs (into #{} (keep member-of) sxs)
        ks (into #{} (keep kind-of) sxs)
        ts (into #{} (keep defined-of) sxs)]
    (when (or (seq ds) (seq xs) (seq ts))
      (swap! (reasoning/nogood-candidates kb)
             #(cond-> %
                (seq ds) (update ::decls (fnil into #{}) ds)
                (seq xs) (update ::terms (fnil into #{}) xs)
                (seq ks) (update ::kinds (fnil into #{}) ks)
                (seq ts) (update ::defns (fnil into #{}) ts))))))

(defn declares-any?
  "Does any stored declaration name a predicate (`tax/arg-declaration-props`)?"
  [tax]
  (boolean (some #(seq (tax/props tax %)) (vals tax/arg-declaration-props))))

(defn installed!
  "Mark the family of a just-installed reasoning image adopted (`::adopt`) when the image
  carries no `::read-under`, as an image written by a build without this family does.  The
  first drain then records the generations it reads under and decides only the queued
  declarations and terms, so the open runs no whole read and every stored fact keeps the
  label the image gives it until a write reaches it, as `:recover? :trust` keeps every
  other label (docs/storage.md, \"Trusting an image\").  `recover` reads it whole."
  [kb]
  (swap! (reasoning/nogood-candidates kb)
         #(if (or (contains? % ::read-under) (::owed %)) % (assoc % ::adopt true))))

(defn moved?
  "Does the drain owe a read: a queued declaration, term or definition, a recover, an
  adopted image's first drain, or taxonomy generations `read-under` other than the last drain's,
  while some fact is held or some declaration is stored?"
  [tax c read-under]
  (boolean (or (::owed c) (::adopt c) (seq (::decls c)) (seq (::terms c)) (seq (::kinds c)) (seq (::defns c))
               (and (not= read-under (::read-under c))
                    (or (seq (::held c)) (declares-any? tax))))))

(defn take!
  "The queue since the last call, emptied, with the taxonomy generations `read-under` recorded:
  `{:decls #{[P context]} :terms #{x} :kinds #{P} :defns #{T} :from old-read-under :owed? bool}`.  An
  adopted image's first call answers `read-under` itself as `:from` (`installed!`)."
  [kb read-under]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb)
                            #(-> % (dissoc ::decls ::terms ::kinds ::defns ::owed ::adopt) (assoc ::read-under read-under)))]
    {:decls (::decls old #{}) :terms (::terms old #{}) :kinds (::kinds old #{}) :defns (::defns old #{})
     :from  (if (::adopt old) read-under (::read-under old)) :owed? (boolean (::owed old))}))

(def family
  "The argument family's entry in `decide/registry`: the write hook that queues what a
  write can move (`note!`).  A recover empties `::held` and owes a whole read."
  {:note!     (fn [kb _w sx stored?] (note! kb sx stored?))
   :recovered (fn [kb _]
                (swap! (reasoning/nogood-candidates kb) #(-> % (dissoc ::held) (assoc ::owed true))))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N10 :label "Argument holds" :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:index :records :M1 :T1 :J5]
  :retired-by {:stored :K :removed :K :relabelled :K :edge :G :edge-belief :G
               :settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates ::held] [:nogood-candidates ::decls] [:nogood-candidates ::terms]
       [:nogood-candidates ::kinds] [:nogood-candidates ::defns] [:nogood-candidates ::read-under] [:nogood-candidates ::owed] [:nogood-candidates ::adopt]]
  :bound "one entry per stored fact or rule held for an argument conviction, one per declaration, per membership term, per `type_relation_predicate` member and per defined type stored, removed or relabelled since the last settle pass"
  :note "the stored facts and rules held in `:out` for an argument conviction (`checks/argument-conviction`), recorded as a fact or rule is stored and at each drain; the declarations, membership terms, `type_relation_predicate` members and defined types a write or relabel queued, and the taxonomy generations the last drain read, which the settle drains (`checks/refresh-argument-holds!`); a recover owes a whole read (`::owed`), and an installed image carrying no generations is adopted as read (`::adopt`)"})
