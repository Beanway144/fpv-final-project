import .sets

namespace zfc
open tactic
/-
__Axiom Tactics__
This file contains a few tactics relating to the axioms of ZFC in sets.lean. While not particularly
useful, these tactics might be helpful in very specific scenarios. Here is an elevator pitch for each
one:

`by_axiom` This tactic allows you to easily solve a goal by applying the axioms of ZFC. Wow!

`list_axioms` Did you forget which axiomatic system you're working in again? Don't worry! This
  tactic shows you all of the axioms.

`explain_axioms` Why go into the sets.lean file when the sets.lean file can come to you? Use this
  tactic to see the gist of each axiom.

-/


/-__by_axiom__
  This tactic attempts to solve the current goal by applying an axiom. -/
meta def by_axiom : tactic unit :=
    ((do applyc `zfc.extensionality, trace "Applied Axiom of Extensionality", skip)  <|>
    (do applyc `zfc.pairing, trace "Applied Axiom of Pairing", skip) <|>
    (do applyc `zfc.separation, trace "Applied Axiom of Separation", skip) <|>
    (do applyc `zfc.empty_set, trace "Applied Axiom of Empty Set", skip) <|>
    (do applyc `zfc.union, trace "Applied Axiom of Union", skip) <|>
    (do applyc `zfc.power_set, trace "Applied Axiom of Power Set", skip) <|>
    (do applyc `zfc.infinity, trace "Applied Axiom of Infinity", skip) <|>
    (do applyc `zfc.replacement, trace "Applied Axiom of Replacement", skip) <|>
    (do applyc `zfc.regularity, trace "Applied Axiom of Regularity", skip) <|>
    (do applyc `zfc.choice, trace "Applied Axiom of Choice", skip)) <|>
    fail "Could not apply ZFC axioms to current state. Instead, enjoy this poem I wrote
    Roses are red,
    Violets are blue,
    ZFC is cool, I guess,
    But no one's as cool as you <3 B)"

/-__list_axioms__
  This tactic lists the axioms of ZFC that are implemented. -/
meta def list_axioms : tactic unit :=
  trace "-List of ZFC Axioms-
  Extensionality - `zfc.extensionality`
  Pairing        - `zfc.pairing`
  Separation     - `zfc.separation`
  Empty Set      - `zfc.empty_set`
  Union          - `zfc.union`
  Power Set      - `zfc.power_set`
  Infinity       - `zfc.infinity`
  Replacemnt     - `zfc.replacement`
  Regularity     - `zfc.regularity`
  Choice         - `zfc.choice`"

/-__list_axioms__
  This tactic attempts to explain each axiom.-/
meta def explain_axioms : tactic unit :=
  trace 
  "<><>Extensionality<><>
  If two sets have the same elements, they are equal.

  <><>Pairing<><>
  Given two sets, there exists a set with only those two sets as elements.

  <><>Separation<><>
  Given some proposition P, we can separate some set into a subset whose elements all satisfy P.

  <><>Empty Set<><>
  There exists a set that has no elements.

  <><>Union<><>
  For any set X, there exists a set whole elements are all elements of elements of X. 

  <><>Power Set<><>
  For any set X, there exists a set P(X) that is the collection of all subsets of X. 

  <><>Infinity<><>
  There exists a set that can be built inductively, starting with the empty set and adding the union of elements of the set to the set.

  <><>Replacement<><>
  If F is a function on the set X, then the image F(X) is also a set.

  <><>Regularity<><>
  Every set has a minimal element with respect to ∈ (sets can't contain themselves).

  <><>Choice<><>
  For any nonempty set, there exists a function that returns an element of that set. 
  "

/-__Examples__-/
-- lemma example1 : (∀(s : Set), ∃(t : Set), ∀(sel sel_el tel: Set), 
--   sel ∈ s → sel_el ∈ sel → tel ∈ t ↔ sel_el = tel) ∧ (∀(s: Set) (φ : Set → Set),
--    (∀(x y a : Set), x ∈ s ∧ φ(x) = y → φ(x) = a ↔ a = y) → ∃(t : Set), ∀(z x: Set),
--     x ∈ s → z ∈ t ↔ φ(x) = z) :=
--   begin
--     split,
--     repeat {by_axiom},
--   end

-- lemma example2 : true :=
--   begin
--     list_axioms,
--     by_axiom, --fails
--   end
end zfc