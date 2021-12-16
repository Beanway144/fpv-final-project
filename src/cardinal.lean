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

/-
Argument:
Let `f` be a function from `X` to `P(X)`. Let `Y = {x ∈ X : ¬x ∈ f(x)}`. Let `I` be the
image of `f`. Then `¬Y ∈ I`. Let `z ∈ X` be such that `f(z) = Y`. Then `z ∈ Y ↔ ¬z ∈ Y`
-/
theorem Cantor : ∀(X : Set), ¬(P(X) ≃ X) :=
  begin
    intros X,
    intro p,
    rw cardinality_eq at p,
    have f : Set → Set := classical.some p,                        -- have f be some function from x -> P(X)
    have pY := (separation (λx, ¬x ∈ f(x)) X),
    have Y : Set := classical.some pY,                             -- have Y be a the set of all x ∈ X not
    have hY := classical.some_spec pY,                             -- in the image of f

    have pI := (separation (λx, x ∈ f(x)) X),
    have I : Set := classical.some pI,                             -- have I be the image of f
    have hI := classical.some_spec pI,

    have pzC := (separation (λx, f(x) = Y) X),                     -- the class where z (the only element) resides
    have zC : Set := classical.some pzC,
    have pz := (separation (λx, x ∈ zC) X),
    have z := classical.some pz,                                    -- suppose z is such that f(z) = Y
    simp at *,
    have hziy : z ∈ Y ↔ ¬z ∈ Y,
    {
      apply iff.intro,
        -- z ∈ Y → ¬z ∈ Y
      { -- I want to show: since z ∈ Y, ¬z ∈ I. but, f(z) = Y, so z ∈ I ...--but, f(z) = Y, so z ∈ I
        intro ziy, -- "since z ∈ Y"
        intro ziy2,
        have z_not_in_I : ¬z ∈ I, -- "¬z ∈ I."
        {
          intro z_in_I,
          have z_in_fz : z ∈ f(z) :=
            begin
              have hIR := iff.elim_left (hI z),
              have help := hIR z_in_I, --__Why can't I do this?__
            end,
          have z_not_in_fz : ¬z ∈ f(z) :=
            begin
              sorry
            end,
            contradiction,     
        },
        have fz_is_Y : f(z) = Y :=
          begin
            sorry
          end,
        have z_in_I : z ∈ I :=
          begin
            sorry
          end,
        contradiction,
      },
      {
        intro not_z_in_Y,
        have z_in_fz : z ∈ f(z) :=
          begin
            sorry
          end,
        have fz_is_Y : f(z) = Y :=
          begin
            sorry
          end,
        have z_in_Y : z ∈ Y :=
          begin
            sorry
          end,
        contradiction,
      },
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