import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

/- NOTE: ft_valid and reachable_valid will take a moment for Lean to process. -/

section ValidityChecks

lemma r_valid : R ∈ ValidCube :=
  by
    simp [R, ValidCube]
    decide

lemma ft_valid : ∀x : RubiksSuperType, FaceTurn x → x ∈ ValidCube :=
  by
    intro x hx
    cases hx with
    | _ =>
      simp [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
      decide

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
    simp [CornerTwist, ValidCube]
    decide

lemma edge_flip_invalid : EdgeFlip ∉ ValidCube :=
  by
    simp [EdgeFlip, ValidCube]
    decide

end ValidityChecks

/- This theorem shows that the set of valid cube states as defined in terms of permutations and orientations of the pieces contains all positions reachable with standard Rubik's cube moves. Further showing that these two sets are in fact the same is equivalent to providing a solution algorithm for any valid cube state. I do not have a proof that the solution algorithm in `SolutionAlgorithm.lean` will solve any valid cube, but I am confident that this is the case (assuming no bugs in my concretely defined setup moves). -/
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

-- instance {n : ℕ} {α : Type*} [DecidableEq α] : DecidableEq (Fin n → α) :=
--   fun f g => Fintype.decidablePiFintype f g


lemma solved_is_solved : IsSolved (Solved) := by native_decide
lemma four_rs_solved : IsSolved (R * R * R * R) := by native_decide

lemma corner_twist_unreachable: ¬ Reachable CornerTwist := by
  intro h
  apply reachable_valid at h
  have h' : CornerTwist ∉ ValidCube := corner_twist_invalid
  contradiction
