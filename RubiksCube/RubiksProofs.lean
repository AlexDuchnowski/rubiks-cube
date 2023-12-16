import RubiksCube.RubiksCube
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

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

-- set_option maxHeartbeats 50000

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

def invert : List RubiksSuperType → List RubiksSuperType
  | [] => []
  | c :: cs => invert cs ++ [c⁻¹]

def AYPList : List RubiksSuperType := [R, U', R', U', R, U, R', F', R, U, R', U', R', F, R]

def cornerSetup : Fin 8 → Fin 3 → List RubiksSuperType
  | 0, _ => []
  | 1, 0 => [R, D]
  | 1, 1 => [R2]
  | 1, 2 => [R', F]
  | 2, 0 => [F]
  | 2, 1 => [F2, D]
  | 2, 2 => [R']
  | 3, 0 => [F, R']
  | 3, 1 => [F2]
  | 3, 2 => [F', D]
  | 4, 0 => [F']
  | 4, 1 => [D]
  | 4, 2 => [F2, R']
  | 5, 0 => [F', R']
  | 5, 1 => []
  | 5, 2 => [D, R]
  | 6, 0 => [D2, F']
  | 6, 1 => [D']
  | 6, 2 => [R]
  | 7, 0 => [D, F']
  | 7, 1 => [D2]
  | 7, 2 => [D', R]

def cornerSwap (corner : Fin 8) (orientation : Fin 3) : List RubiksSuperType :=
  let setup := cornerSetup corner orientation
  setup ++ AYPList ++ (invert setup)

-- def Misoriented {n m : ℕ+} : Fin n → (Fin n → Fin m) → Fin n
--   | 0, _ => 0
--   | x, f => if f x != 0 then x else Misoriented (x - 1) f

def Misoriented {n m : ℕ+} (f : Fin n → Fin m) : Fin n := Id.run do
  let mut out := 0
  for h : i in [1:n] do
    let i : Fin n := ⟨i, h.2⟩
    if f i != 0 then
      out := i
      break
    else continue
  out

-- #eval Misoriented (fun x => 2 : Fin 8 → Fin 3) -- not working...why?

def update : RubiksSuperType → List RubiksSuperType → RubiksSuperType
  | c, [] => c
  | c, u :: us => update (c * u) us

unsafe def solveCorners : RubiksSuperType → List RubiksSuperType := fun c =>
  if CornersSolved c then
    []
  else
    let buffer := c.1.permute 0
    if buffer != 0 then
      let swap := cornerSwap buffer (c.1.orient 0)
      swap ++ solveCorners (update c swap)
    else
      let slot := Misoriented c.1.orient
      let swap := cornerSwap slot 0
      swap ++ solveCorners (update c swap)

-- #eval update L (solveCorners L)

def solveEdges : ValidCube → List ValidCube := fun c => sorry
