import RubiksCube.RubiksCubeVector
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

section ValidityChecks

lemma r_valid : R ∈ ValidCube :=
  by
    simp [R, ValidCube]
    apply And.intro
    { apply Eq.refl }
    { native_decide }

lemma ft_valid : ∀x : RubiksSuperType, FaceTurn x → x ∈ ValidCube :=
  by
    intro x hx
    cases hx with
    | _ =>
      simp [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
      repeat' apply And.intro
      all_goals apply Eq.refl

lemma tperm_valid : TPerm ∈ ValidCube :=
  by
    simp [TPerm]
    repeat apply RubiksGroup.mul_mem'
    all_goals apply ft_valid
    { apply FaceTurn.R }
    { apply FaceTurn.U }
    { apply FaceTurn.R' }
    { apply FaceTurn.U' }
    { apply FaceTurn.R' }
    { apply FaceTurn.F }
    { apply FaceTurn.R2 }
    { apply FaceTurn.U' }
    { apply FaceTurn.R' }
    { apply FaceTurn.U' }
    { apply FaceTurn.R }
    { apply FaceTurn.U }
    { apply FaceTurn.R' }
    { apply FaceTurn.F' }

lemma corner_twist_invalid : CornerTwist ∉ ValidCube :=
  by
    simp [CornerTwist, ValidCube, zeroOrient, Vector.toList, Vector.replicate, Vector.set, List.set]
    exact (bne_iff_ne 3 1).mp (by rfl)

lemma edge_flip_invalid : EdgeFlip ∉ ValidCube :=
  by
    simp [EdgeFlip, ValidCube, zeroOrient, Vector.toList, Vector.replicate, Vector.set, List.set]
    exact (bne_iff_ne 2 1).mp (by rfl)

end ValidityChecks

theorem reachable_valid : ∀x : RubiksSuperType, Reachable x → x ∈ ValidCube := by
  intro x hrx
  induction hrx with
  | Solved =>
      simp [Solved, ValidCube]
      apply And.intro
      { apply Eq.refl }
      { apply And.intro
        { apply Eq.refl }
        { apply Eq.refl } }
  | FT c hc =>
      cases hc with
      | _ =>
          simp [ValidCube]
          apply And.intro
          { apply Eq.refl }
          { apply And.intro
            { apply Eq.refl }
            { apply Eq.refl } }
  | mul x y hrx hry a_ih a_ih_1 =>
      apply RubiksGroup.mul_mem'
      all_goals assumption

lemma solved_is_solved : IsSolved (Solved) := by native_decide
lemma four_rs_solved : IsSolved (R * R * R * R) := by native_decide

lemma corner_twist_unreachable: ¬ Reachable CornerTwist := by
  intro h
  apply reachable_valid at h
  have h' : CornerTwist ∉ ValidCube := corner_twist_invalid
  contradiction
