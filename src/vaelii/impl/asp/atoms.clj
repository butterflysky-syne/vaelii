;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.atoms
  "The atom id table `asp.edge/translate` builds.  Two kinds of value are interned under
  one counter, so ids are unique across kinds and start at 1 (0 is the ASPIF terminator):

    * a sentex id, an atom the solver decides, labelled `s<sentex-id>`;
    * a contradiction descriptor `(contradiction <head> :involved [[:sentex h] …])`, a
      violation atom the minimize statement weighs, labelled `c<atom-id>`.

  A witness reports labels, and each label maps back to its value.  The table is an atom
  over a map, and interning is idempotent.")

(defn new-table
  "Return a fresh empty atom table."
  []
  (atom
   {:counter             0    ; last allocated atom id (0 = none)
    :sentex->atom        {}   ; sentex id → atom id
    :atom->sentex        {}   ; reverse
    :contradiction->atom {}   ; descriptor → atom id
    :atom->contradiction {}   ; reverse
    :atom->label         {}   ; atom id → label string
    :label->atom         {}}))

(defn- intern!
  "Idempotent intern of `value` under `fwd-key`. If absent, allocate a
   fresh atom id, record both forward and reverse mappings, and assign
   a label via `label-fn`. Returns the atom id.

   `label-fn` is called as `(label-fn value assigned-atom-id)` and must
   return a unique non-empty string."
  [table fwd-key rev-key value label-fn]
  (or (get-in @table [fwd-key value])
      (-> (swap! table
                 (fn [{:keys [counter] :as t}]
                   (if (contains? (get t fwd-key) value)
                     t  ; lost the swap race — another caller interned
                     (let [new-id (inc counter)
                           label  (label-fn value new-id)]
                       (-> t
                           (assoc :counter new-id)
                           (assoc-in [fwd-key value] new-id)
                           (assoc-in [rev-key new-id] value)
                           (assoc-in [:atom->label new-id] label)
                           (assoc-in [:label->atom label] new-id))))))
          (get-in [fwd-key value]))))

(defn intern-sentex!
  "Ensure the sentex with id `sentex-id` has an atom id. Returns the
   atom id. Idempotent. Callers that have a sentex record should pass
   `(sentex/id sentex)`."
  [table sentex-id]
  (intern! table :sentex->atom :atom->sentex sentex-id
           (fn [sid _] (str "s" sid))))

(defn intern-contradiction!
  "Ensure `descriptor` has an atom id. `descriptor` is the nested
   sentence-shaped value
     (contradiction <head> :involved [[:sentex H1] [:sentex H2] …])
   so consumers can introspect a witness's contradiction atoms without
   secondary queries."
  [table descriptor]
  (intern! table :contradiction->atom :atom->contradiction descriptor
           (fn [_ atom-id] (str "c" atom-id))))

(defn atom-of-sentex
  "Atom id for `sentex-id`, or nil if not yet interned."
  [table sentex-id]
  (get-in @table [:sentex->atom sentex-id]))

(defn sentex-id-of-atom
  "The sentex id backing `atom-id`, or nil if the atom is not sentex-backed."
  [table atom-id]
  (get-in @table [:atom->sentex atom-id]))

(defn label-of-atom
  "Label string for `atom-id`, or nil."
  [table atom-id]
  (get-in @table [:atom->label atom-id]))

(defn atom-of-label
  "Reverse: given a label string (from a clasp witness), return the
   atom id, or nil if the label is unknown."
  [table label]
  (get-in @table [:label->atom label]))
