import RubiksCube.RubiksCube
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

theorem reachable_valid : ∀x : RubiksSuperType, Reachable x → x ∈ ValidCube := by
  intro x hrx
  induction hrx with
  | mul x y hrx hry a_ih a_ih_1 =>
      simp [ValidCube, PieceState.mul_def, ps_mul]
      aesop
      { have h1 : sign fst_1.permute = sign snd_1.permute := by apply a_ih.left
        have h2 : sign fst_2.permute = sign snd_2.permute := by apply a_ih_1.left
        simp [Perm.sign_mul, h1, h2] }
      { have h1 : Fin.foldl 8 (fun acc n ↦ acc + PieceState.orient (fst_1, snd_1).1 n) 0 = 0 :=   by apply a_ih.right.left
        have h2 : Fin.foldl 8 (fun acc n ↦ acc + PieceState.orient (fst_2, snd_2).1 n) 0 = 0 := by apply a_ih_1.right.left
        sorry }
      { sorry }
  | _ =>  simp [ValidCube]
          apply And.intro
          · apply Eq.refl
          · apply And.intro
            · apply Eq.refl
            · apply Eq.refl

#check Perm.sign_mul

-- instance {n : ℕ} {α : Type*} [DecidableEq α] : DecidableEq (Fin n → α) :=
--   fun f g => Fintype.decidablePiFintype f g

def CornersSolved : RubiksSuperType → Prop :=
  fun c => c.fst.permute = 1 ∧ c.fst.orient = 0

def EdgesSolved : RubiksSuperType → Prop :=
  fun c => c.snd.permute = 1 ∧ c.snd.orient = 0

def IsSolved : RubiksSuperType → Prop := fun c => CornersSolved c ∧ EdgesSolved c

instance {c} : Decidable (CornersSolved c) := by apply And.decidable
instance {c} : Decidable (EdgesSolved c) := by apply And.decidable
instance {c} : Decidable (IsSolved c) := by apply And.decidable


--? Why do both of these pause forever?
-- lemma four_rs_eq_solved : (R * R * R * R) = Solved := by
--   simp [R, Solved]
--   aesop

lemma solved_is_solved : IsSolved (Solved) := by
  simp [IsSolved, CornersSolved, EdgesSolved, Solved]
  apply And.intro
  · apply And.intro
    · apply Eq.refl
    · apply Eq.refl
  · apply And.intro
    · apply Eq.refl
    · apply Eq.refl

set_option maxHeartbeats 50000

lemma four_rs_solved : IsSolved (R * R * R * R) := by
  simp [R, IsSolved, CornersSolved, EdgesSolved, Solved, orientVector, zeroOrient]
  repeat (all_goals apply And.intro)
  { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Equiv.Perm.permGroup.mul_assoc]

    -- have h : swap 1 6 * (swap 6 5 * swap 5 2) *
    -- (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2)))) = swap 1 6 * swap 6 5 * swap 5 2 *
    -- swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 := by apply
    sorry }
  { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Orient]
    sorry }
  { sorry }
  { sorry }

#check Equiv.Perm.permGroup.mul_assoc

def solveCorners : ValidCube → ValidCube := fun c =>
  if CornersSolved c then
    sorry
  else
    sorry

def solveEdges : ValidCube → ValidCube := fun c => sorry
