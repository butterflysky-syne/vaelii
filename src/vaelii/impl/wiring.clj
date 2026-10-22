;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.wiring
  "The calls that run *up* the engine's layering, gathered in one file.

  Every edge in the engine is a static require the compiler checks:

    kb <- checks <- special <- integrate <- chain <- settle <- vaelii.core

  Five targets are reached the other way, and the static require graph cannot express any
  of them.  Four are **genuine mutual recursion**, where the cycle is in the *behaviour* and
  no code motion removes it: the assert path reaches a mint that asserts
  (`assert-sentence`); negation-as-failure runs the prover registry back over its own
  argument (`solve-goal`); the exception read walk asks the claim walk for a second route,
  and the claim walk reads facts through the exception read walk (`route-reach`,
  `firing-goals`, `goal-reach`); and a KB's open replays its operation log through the
  write entry points of `vaelii.core` (`replay-op`).  The fifth, `retract-sentex`, is the
  teardown entry point a below-core solver reaches while the teardown orchestration is
  core-private.  `lein lint`'s **E8** fails a literal `requiring-resolve` anywhere else
  under `src/`, **E19** any target beyond these five, and **E20** a namespace that installs
  a function into a lower namespace's slot at load instead of appearing here.  Each entry
  is a `delay` over `requiring-resolve` rather than a dynamic var.  See docs/namespaces.md,
  \"The layering\".

  `*defer-settle?*` lives here too, because both sides of the assert recursion read it."
  (:refer-clojure :exclude [assert]))

;; ---- the write-path mode flag --------------------------------------------
;; It lives here rather than with the write path because both sides of the recursion read
;; it: `vaelii.core`'s assert decides whether to settle by it, and `skolem` binds it around
;; a mint to say "not now — I am inside the fixpoint you are about to settle".  Down here
;; both can see it without either naming the other.

(def ^:dynamic *defer-settle?*
  "When true, the assert path does **not** `settle` after storing — belief is left
  un-reconciled for the caller to settle once, later.  Three callers bind it:

  - a rule firing minting a skolem NAT mid-fixpoint (`vaelii.impl.skolem`): the nested
    `(natFormula K E)` assert is monotonic bookkeeping and the enclosing firing settles
    once when it finishes, so settling per mint would be redundant churn — and worse,
    would relabel belief inside the running chain (docs/skolem.md);
  - a placed conclusion minting the constants of its ground reifiable NATs
    (`vaelii.impl.chain/reify-conclusion`), a reduced `Quasiquote`'s `(Quote E)` among
    them, which is the same mint inside the same fixpoint and defers for the same reason;
  - `with-deferred-settle` / `assert-many`, which run a whole batch of asserts under it
    and settle once at the end, so a bulk load pays one belief reconciliation instead of
    N.  Chaining still runs per assert (only the `settle` is deferred), so the final
    settle sees the same stored state a per-assert settle would have, and order
    independence guarantees the same beliefs.

  Retraction settles eagerly regardless — reviving a defeated default is not part of an
  assert batch."
  false)

;; ==== Genuine mutual recursion ============================================

;; `assert-sentence` runs the full assertion path.  Four namespaces call it from inside
;; the chaining fixpoint `vaelii.core/assert` itself started: `vaelii.impl.nat` (a reified
;; NAT stores its `(natFormula K E)` map and its materialized types), `vaelii.impl.skolem`
;; (a firing mints its witness), `vaelii.impl.quasiquote` (declaring the four marks
;; quasiquotation runs on) and `vaelii.impl.chain` (`reassert-premise` re-asserts a premise
;; under the spelling a predicate declaration folds it to).  `vaelii.impl.asp.label` and
;; `vaelii.impl.asp.solve-context` call it outside chaining, to store a labeling's
;; sentences and its `genlCx` edge, for `retract-sentex`'s reason below.  Storing is a
;; *whole* assert — naming, the definitional checks, the index, chaining, settle — so the
;; write path runs chaining, and chaining calls back here to mint a constant.  The cycle is in the behaviour, and no arrangement of the code
;; removes it (docs/skolem.md).

(def ^:private core-assert
  (delay (requiring-resolve 'vaelii.core/assert)))

(defn assert-sentence
  "`vaelii.core/assert` — store `sentence` in `context` under `opts`, returning its handle."
  [kb sentence context opts]
  (@core-assert kb sentence context opts))

;; `solve-goal` is the prover registry's entry point.  `vaelii.impl.resolution` calls it to
;; discharge a deferred antecedent (`different` / `evaluate` / `unknown`).  `vaelii.impl.provers`
;; already requires `resolution`, so `resolution` cannot name `provers/solve-goal` at compile
;; time.  Backward chaining is a leaf the registry dispatches to, and `unknown` runs the
;; registry back over its own argument, so negation-as-failure is mutually recursive with the
;; chainer that asked for it (docs/naf.md).

(def ^:private provers-solve-goal
  (delay (requiring-resolve 'vaelii.impl.provers/solve-goal)))

(defn solve-goal
  "`vaelii.impl.provers/solve-goal` — the registry's raw solution bindings for `goal` in
  `context`."
  [kb goal context]
  (@provers-solve-goal kb goal context))

;; The second-route walks.  `vaelii.impl.except`'s read walk asks whether a reader reaches a
;; preserved claim's path, or a rule firing's goals, another way, and
;; `vaelii.impl.inherit`'s claim walk answers.  `inherit` requires `except`, and the claim
;; walk matches facts through `res/matches-visible`, which reads the excepts back through
;; `except`'s read walk: the two walks are mutually recursive, and `except/*routes*` bounds
;; the nesting.  A `requiring-resolve` loads `inherit` on first use, so the answer does not
;; depend on which namespace loaded first.

(def ^:private inherit-second-route
  (delay (requiring-resolve 'vaelii.impl.inherit/second-route)))

(defn route-reach
  "Does `reader` reach `b` from `a` over the fact relation `rel` a `transitiveInArgInverse`
  preserves a claim along?"
  [kb rel a b reader]
  ((:reach @@inherit-second-route) kb rel a b reader))

(defn firing-goals
  "`[goals stated]` for the rule firing `j`: the goals it matched through a reach and the
  antecedent handles that state a literal, or nil when it reads no goal off `j`."
  [kb j]
  ((:goals @@inherit-second-route) kb j))

(defn goal-reach
  "Does `reader` reach the ground `goal` from a claim it reads?"
  [kb goal reader]
  ((:goal-reach @@inherit-second-route) kb goal reader))

;; `replay-op` is the operation-log replay table.  `vaelii.core/open-kb` opens a sealed store
;; through `vaelii.impl.seal`, which replays the frames logged since the seal through
;; `vaelii.impl.oplog/replay!`, and each frame runs the `vaelii.core` write entry point that
;; recorded it.  The open and the entry points are mutually recursive through the log.

(def ^:private core-replay-dispatch
  (delay (requiring-resolve 'vaelii.core/replay-dispatch)))

(defn replay-op
  "The function a logged frame of operation `op` runs through, or nil when `vaelii.core`
  records no such operation."
  [op]
  (get @@core-replay-dispatch op))

;; `retract-sentex` is the teardown entry point.  `vaelii.impl.asp.solve-context` reaches it
;; to retract a labeling artifact (an inert truth value, its `genlCx` placement edge).
;; Unlike the four above this is **not** a behavioural cycle: the teardown orchestration
;; (`retract-storage!`, the settle, the orphan and meta sweeps) is core-private and has not
;; been extracted below `vaelii.core`, so a below-core caller reaches it up here.  Extracting
;; that orchestration below core would let this point downward like the others, and is the
;; only reason the entry lives here rather than as an ordinary require.

(def ^:private core-retract
  (delay (requiring-resolve 'vaelii.core/retract!)))

(defn retract-sentex
  "`vaelii.core/retract!` — retract premise support for `handle`, tearing down
  solely-supported sentexes and justifications and reversing their taxonomy / rule-index
  effects; returns counts."
  [kb handle]
  (@core-retract kb handle))
