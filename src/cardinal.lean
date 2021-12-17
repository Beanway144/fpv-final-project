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
  (λ(x y : Set), ∃(f : Set → Set),
    (∀a b, a ∈ x ∧ b ∈ x → (a ≠ b → f(a) ≠ f(b)))          -- injection
    ∧ (∀c, c ∈ y → ∃d, d ∈ x ∧ f(d) = c)                   -- surjection
  )
infix ` ≃ ` : 110 := cardinality_eq

/- _Cantor's Theorem_: X ≢ P(X) : A set does not have the same cardinality as its power set. -/
/-Argument Structure:
Let `f` be a bijection from `X` to `P(X)`. Let `Y = {x ∈ X : ¬x ∈ f(x)}`.
Let `z ∈ X` be such that `f(z) = Y`. Then `z ∈ Y ↔ ¬z ∈ Y`. Contradiction!
-/
theorem Cantor : ∀(X: Set), ¬(X ≃ P(X)) :=
  begin
    intro X,
    intro p,
    rw cardinality_eq at p,

    /-Have `f` be some bijection from `X` to `P(X)`.-/
    let f : Set → Set := classical.some p,

    /-Have `Y = {x ∈ X : ¬x ∈ f(x)}`.-/
    have pY := (separation (λx, ¬x ∈ f(x)) X),
    let Y : Set := classical.some pY,
    have hY := classical.some_spec pY,

    /-Have `I = {x ∈ X : x ∈ f(x)}`.-/
    have pI := (separation (λx, x ∈ f(x)) X),
    let I : Set := classical.some pI,
    have hI := classical.some_spec pI,

    /-Let `zC` be the class of sets that contain all sets `z` such that `f(z) = Y`.
      (zC really only contains one element.)-/
    have pzC := (separation (λx, f(x) = Y) X),
    let zC : Set := classical.some pzC,
    have hzC := classical.some_spec pzC,

    have zC_nonempty : ∃z, z ∈ zC :=
      begin
        have exists_z : ∃x, x ∈ X ∧ f(x) = Y :=
          begin
            have hp := classical.some_spec p,
            have f_is_surj := and.elim_right hp Y,
            have Y_in_PX : Y ∈ P(X) :=
              begin
                have Y_subset_X : Y ⊂ X :=
                  begin
                    rw is_subset,
                    intros x x_in_Y,
                    have j := iff.elim_left (hY x),
                    apply and.elim_left (j x_in_Y),
                  end,
                rw [P, power_set_of],
                simp,
                have hPX := iff.elim_right (classical.some_spec (power_set X) Y),
                apply hPX Y_subset_X,
              end,
            apply f_is_surj Y_in_PX,
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

    /-Have `z` be some (the) element of `zC`.-/
    let z := classical.some zC_nonempty,
    have hz := classical.some_spec zC_nonempty,

    have z_in_zC : z ∈ zC := by apply hz,

    have z_in_X : z ∈ X :=
      begin
        have hzCR := iff.elim_left (hzC z) z_in_zC,
        apply and.elim_left hzCR,
      end,

    simp at *,

    /- We can show that __z ∈ Y ↔ ¬z ∈ Y__. -/
    have hziy : z ∈ Y ↔ ¬z ∈ Y,
    {
      apply iff.intro,
      {
        /- Forward Direction: z ∈ Y → ¬z ∈ Y
        If z ∈ Y, then ¬z ∈ I. But, f(z) = Y, so z ∈ I. Contradiction, thus ¬z ∈ Y. -/
        intro ziy,
        intro ziy2,
        have z_not_in_I : ¬z ∈ I,
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
        /-Backward Direction: ¬z ∈ Y → z ∈ Y
        If ¬z ∈ Y, then z ∈ f(z). But f(z) = Y, so z ∈ Y.-/
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
    /-Uh-oh! We have that z ∈ Y ↔ ¬z ∈ Y. We can break into cases, and say that if
      z ∈ Y, then we have a contradiction, and if ¬z ∈ Y, we also have a contradiction.-/
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