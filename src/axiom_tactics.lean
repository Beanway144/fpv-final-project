import .sets

namespace zfc
open tactic

/-__by_axiom__
  This tactic attempts to solve the current goal by applying an axiom. -/
meta def by_axiom : tactic unit :=
    ((do applyc `zfc.extensionality, trace "Applied Axiom of Extensionality", skip)  <|>
    (do applyc `zfc.pairing, trace "Applied Axiom of Pairing", skip) <|>
    (do applyc `zfc.separation, trace "Applied Axiom of Separation", skip) <|>
    (do applyc `zfc.empty_set, trace "Applied Axiom of Empty Set", skip) <|>
    (do applyc `zfc.union, trace "Applied Axiom of Union", skip) <|>
    (do applyc `zfc.power_set, trace "Applied Axiom of Power Set", skip) <|>
    --do applyc `zfc.infinity, trace "Applied Axiom of Infinity", skip <|>
    do applyc `zfc.replacement, trace "Applied Axiom of Replacement", skip <|>
    do applyc `zfc.regularity, trace "Applied Axiom of Regularity", skip <|>
    do applyc `zfc.choice, trace "Applied Axiom of Choice", skip) <|>
    fail "Could not apply ZFC axioms to current state. Instead, enjoy this poem I wrote
    Roses are red,
    Violets are blue,
    ZFC is cool, I guess,
    But no one's as cool as you <3 B)"

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


meta def explain_axioms : tactic unit :=
  trace 
  "<><>Extensionality<><>
  If two sets have the same elements, they are equal.

  <><>Pairing<><>
  Given two sets, there exists a set with only those two sets as elements.

  <><>Separation<><>aa
  "


lemma example1 : ∀(s x: Set) (φ : Set → Set), x ∈ s ∧ ∃!(y : Set), φ(x) = y →
  ∃(t : Set), ∀(z : Set), z ∈ t ↔ φ(x) = z :=
  begin
    by_axiom,
  end

lemma example2 : true :=
  begin
    list_axioms,
    by_axiom,
  end
end zfc