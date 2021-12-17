import .sets
import .axiom_tactics
import .lovelib
namespace zfc
namespace LoVe

/------------------------------------__Cardinality__------------------------------------/
/-  The cardinality of a set invokes its notion of size. Two sets are cardinally equal -/
/-                     if there exists a bijection between them.                       -/

/- Two sets `x` and `y` have the same cardinality if there exists
   a bijective function `f` from `x` to `y`.-/
def cardinality_eq : Set → Set → Prop :=
  -- (λ(x y : Set), ∃(f : Set → Set), f(x) = y →
  --   (∀(a : Set), f(x) = a ↔ a = y) ∧ (∀(b : Set), f(b) = y ↔ x = b))
  (λ(x y : Set), ∃(f : Set → Set),
    (∀a b, a ∈ x ∧ b ∈ x ∧ (a ≠ b → f(a) ≠ f(b)))          -- injection
    ∧ (∀c, c ∈ y ∧ ∃d, d ∈ x ∧ f(d) = c)                   -- surjection
  )
infix ` ≃ ` : 110 := cardinality_eq

/- _Cantor's Theorem_: X ≢ P(X) ; A set does not have the same cardinality as its power set. -/
/-Argument Structure:
Let `f` be a function from `X` to `P(X)`. Let `Y = {x ∈ X : ¬x ∈ f(x)}`. Let `I` be the
compliment of `Y`. Let `z ∈ X` be such that `f(z) = Y`. Then `z ∈ Y ↔ ¬z ∈ Y`.
-/
theorem Cantor : ∀(X : Set), ¬(X ≃ P(X)) :=
  begin
    intros X,
    intro p,
    rw cardinality_eq at p,
    let f : Set → Set := classical.some p,                        -- have f be some function from x -> P(X)
    have pY := (separation (λx, ¬x ∈ f(x)) X),
    let Y : Set := classical.some pY,                             -- have Y be a the set of all x ∈ X not
    have hY := classical.some_spec pY,                             -- in the image of f

    have pI := (separation (λx, x ∈ f(x)) X),
    let I : Set := classical.some pI,                             -- have I be the image of f
    have hI := classical.some_spec pI,

    have pzC := (separation (λx, f(x) = Y) X),                     -- the class where z (the only element) resides
    let zC : Set := classical.some pzC,
    have hzC := classical.some_spec pzC,

    have thing : ∃z, z ∈ zC :=
      begin
        have exists_z : ∃x, x ∈ X ∧ f(x) = Y :=
          begin
            have hp := classical.some_spec p,
            have f_is_surj := and.elim_right hp Y,
            apply and.elim_right f_is_surj,
          end,
        let a := classical.some exists_z,
        have hzCL := iff.elim_right (hzC a),
        have ha := classical.some_spec exists_z,
        simp at hzCL,
        have a_in_X : a ∈ X := by apply and.elim_left ha,
        have fa_is_Y : f a = Y := by apply and.elim_right ha,
        have a_in_zC := (hzCL a_in_X) fa_is_Y,
        apply exists.intro a,
        assumption,
      end,
    let z := classical.some thing,
    have hz := classical.some_spec thing,

    have z_in_zC : z ∈ zC := by apply hz,

    have z_in_X : z ∈ X :=
      begin
        have hzCR := iff.elim_left (hzC z) z_in_zC,
        apply and.elim_left hzCR,
      end,

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
              have hIR := iff.elim_left (hI z) z_in_I,
              apply and.elim_right hIR,
            end,
          have z_not_in_fz : ¬z ∈ f(z) :=
            begin
              have hYR := iff.elim_left (hY z) ziy,
              apply and.elim_right hYR,
            end,
            contradiction,     
        },
        have fz_is_Y : f(z) = Y :=
          begin
            have hzCR := iff.elim_left (hzC z),
            apply and.elim_right (hzCR z_in_zC),
          end,
        have z_in_I : z ∈ I :=
          begin
            have z_in_fz : z ∈ f(z) :=
              begin
                simp [fz_is_Y, ziy],
              end,
            have hIL := iff.elim_right (hI z),
            apply (hIL (and.intro z_in_X z_in_fz)),
          end,
        contradiction,
      },
      {
        intro not_z_in_Y,
        have z_in_fz : z ∈ f(z) :=
          begin
            have hYR := iff.elim_right (hY z),
            have nhY := not.imp not_z_in_Y hYR,
            simp at nhY,
            simp [nhY, z_in_X],
          end,
        have fz_is_Y : f(z) = Y :=
          begin
            have hzCR := iff.elim_left (hzC z),
            apply and.elim_right (hzCR z_in_zC),
          end,
        have z_in_Y : z ∈ Y :=
          begin
            rw (eq.symm fz_is_Y),
            exact z_in_fz,
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
  end

end LoVe
end zfc