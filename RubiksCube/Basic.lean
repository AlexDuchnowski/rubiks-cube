import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

section RubiksGroup

open Equiv Perm

def PiecesType (pieces orientations: ℕ) := (Perm (Fin pieces) × Vector (Fin orientations) pieces)

instance PieceGroup (pieces orientations: ℕ) :
Group (PiecesType pieces orientations) := {
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
}

abbrev VertexType := PiecesType 8 3
abbrev EdgeType := PiecesType 12 2

instance RubiksSuperGroup : Group (VertexType × EdgeType) := Prod.instGroup
