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
  Infinity       - `zfc.replacement`
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

  <><>Separation<><> TODO i should probably finish this or delete since its useless idk idk
  "


-- lemma example1 : ∀(s x: Set) (φ : Set → Set), x ∈ s ∧ ∃!(y : Set), φ(x) = y →
--   ∃(t : Set), ∀(z : Set), z ∈ t ↔ φ(x) = z :=
--   begin
--     by_axiom,
--   end

-- lemma example2 : true :=
--   begin
--     list_axioms,
--     by_axiom,
--   end
end zfc