import .sets
import .axiom_tactics
import .lovelib
namespace zfc
namespace LoVe

/- Two sets `x` and `y` have the same cardinality if there exists
   a bijective function `f` from `x` to `y`.-/
def cardinality_eq : Set → Set → Prop :=
  (λ(x y : Set), ∃(f : Set → Set), f(x) = y →
    (∀(a : Set), f(x) = a ↔ a = y) ∧ (∀(b : Set), f(b) = y ↔ x = b))
infix ` ≃ ` : 110 := cardinality_eq

/- Proof that the empty set is empty. Also known as the fields medal-
   winning Benway Theorem. -/
lemma empty_is_empty : ∀s, ¬(s ∈ empty) :=
  begin
    apply classical.some_spec empty_set,
  end

/-
Argument:
Let `f` be a function from `X` to `P(X)`. Let `Y = {x ∈ X : ¬x ∈ f(x)}`. Let `I` be the
image of `f`. Then `¬Y ∈ I`. Let `z ∈ X` be such that `f(z) = Y`. Then `z ∈ Y ↔ ¬z ∈ Y`
-/
theorem Cantor : ∀(X : Set), ∃x, x ∈ X → ¬(P(X) ≃ X) :=
  begin
    intros X,
    apply exists.intro,
    intros hX p,
    rw cardinality_eq at p,
    have f : Set → Set := classical.some p,                        -- have f be some function from x -> P(X)
    have pY := (separation (λx, ¬x ∈ f(x)) X),
    have Y : Set := classical.some pY,                             -- have Y be a the set of all x ∈ X not
    have hY := classical.some_spec pY,                             -- in the image of f

    have pI := (separation (λx, x ∈ f(x)) X),
    have I : Set := classical.some pI,                             -- have I be the image of f
    have hI := classical.some_spec pI,

    have pz := (separation (λx, f(x) = Y) X),
    have z : Set := classical.some pz,  -- suppose z is such that f(z) = Y
    simp at *,
    have hziy : z ∈ Y ↔ ¬z ∈ Y,
    {
      apply iff.intro,
      {
        intro ziy,
        have hY2 : ∀ (u : Set), u ∈ Y ↔ u ∈ X ∧ (λ (x : Set), ¬x ∈ f x) u,
        {
          simp [pY],
          
        }
      },
      {
        sorry
      }
    },
    have uhoh : z ∈ Y ∨ ¬z ∈ Y := by apply classical.em,
    apply or.cases_on uhoh,
    {
      intro ziy,
      have zniy : ¬z ∈ Y,
      {
        apply iff.elim_left hziy,
        assumption,
      },
      contradiction
    },
    {
      intro nziy,
      have ziy : z ∈ Y,
      {
        apply iff.elim_right hziy,
        assumption
      },
      contradiction
    },
    assumption,
  end

end LoVe
end zfc