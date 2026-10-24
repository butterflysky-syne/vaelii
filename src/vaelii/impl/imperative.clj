;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.imperative
  "The `do/` imperatives: an instruction given to `assert`, which dispatches it here
  (`run`) before any naming or well-formedness check.  The form is never stored.  Each
  backing fn is resolved by symbol on first use, so loading `vaelii.core` loads no
  `vaelii.impl.asp.*` namespace.  See docs/labeling.md, \"The `do/` channel\"."
  (:require [clojure.string :as str]))

(defn- imperative-fn
  "Resolve the function backing a `do/` imperative, or throw naming the ones there are."
  [functor]
  (let [known {'do/labeling 'vaelii.impl.asp.label/label-dilemmas
               'do/label    'vaelii.impl.asp.solve-context/label
               'do/classify 'vaelii.impl.asp.solve-context/classify}]
    (if-let [sym (known functor)]
      (or (requiring-resolve sym)
          (throw (ex-info (str "imperative " functor " is backed by " sym
                               ", and that namespace defines no such var")
                          {:type :not-assertible :form functor :wanted sym})))
      (throw (ex-info (str "unknown imperative " functor
                           "; known: " (str/join ", " (sort (map str (keys known)))))
                      {:type :not-assertible :form functor :known (set (keys known))})))))

(defn run
  "Run a `do/` imperative and return its result map, not a handle:
  `(do/labeling Ctx [Base])` → `label/label-dilemmas`, `(do/label Base Into [mode])` →
  `solve-context/label`, `(do/classify Into)` → `solve-context/classify`.  Throws
  `:not-assertible` for an unknown imperative or ill-shaped arguments."
  [kb sentence context]
  (let [[functor & args] sentence
        f (imperative-fn functor)
        ctx-arg? (fn [x] (and x (symbol? x)))]
    (case functor
      do/labeling (let [[ctx base] args]
                    (when-not (and (ctx-arg? ctx) (or (nil? base) (symbol? base))
                                   (<= (count args) 2))
                      (throw (ex-info (str "(do/labeling Ctx [Base]) wants one or two"
                                           " context names, got " (pr-str (vec args)))
                                      {:type :not-assertible :sentence sentence})))
                    (f kb ctx (or base context)))
      do/label    (let [[base into-cx mode] args]
                    (when-not (and (ctx-arg? base) (ctx-arg? into-cx)
                                   (or (= 2 (count args))
                                       (and (= 3 (count args)) (#{:one :sat :all} mode))))
                      (throw (ex-info (str "(do/label Base Into [:one|:sat|:all]) wants"
                                           " two context names and an optional mode of"
                                           " :one, :sat or :all, got "
                                           (pr-str (vec args)))
                                      {:type :not-assertible :sentence sentence})))
                    (f kb base into-cx (or mode :all)))
      do/classify (let [[into-cx] args]
                    (when-not (and (ctx-arg? into-cx) (= 1 (count args)))
                      (throw (ex-info (str "(do/classify Into) wants one context name,"
                                           " got " (pr-str (vec args)))
                                      {:type :not-assertible :sentence sentence})))
                    (f kb into-cx)))))
