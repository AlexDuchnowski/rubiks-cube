import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

section RubiksGroup

open Equiv Perm

def permuteVector {α : Type} {n : ℕ} : Perm (Fin n) → Vector α n → Vector α n :=
  fun p v => {
    val := (Vector.ofFn (fun i => v.get (p.invFun i))).toList
    property := by simp
  }

structure PieceState (pieces orientations: ℕ+) :=
  (permute : Perm (Fin pieces))
  (orient : Vector (Fin orientations) pieces)

-- def PieceState' (pieces orientations: ℕ) := (Perm (Fin pieces) × Vector (Fin orientations) pieces)

def mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
  fun a b => {
    permute := b.permute * a.permute
    orient := Vector.map₂ (fun x y => x + y) (permuteVector b.permute a.orient) b.orient
  }

-- variable {p o : ℕ+}

-- instance: Mul (PieceState p o) := mul

lemma ps_mul_assoc {p o : ℕ+} : ∀ (a b c : PieceState p o), mul (mul a b) c = mul a (mul b  c) := by
  intro a b c
  simp [mul]
  apply And.intro
  { simp [Perm.mul_def, Equiv.trans_assoc] }
  { simp [permuteVector]
    sorry }

lemma ps_one_mul {p o : ℕ+} : ∀ (a : PieceState p o), mul {permute := 1, orient := Vector.replicate p 0} a = a := by
  intro a
  simp [mul, permuteVector]
  sorry

instance PieceGroup (pieces orientations: ℕ+) :
Group (PieceState pieces orientations) := {
  mul := mul
  mul_assoc := ps_mul_assoc
  one := {permute := 1, orient := Vector.replicate pieces 0}
  one_mul := ps_one_mul
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
}

abbrev VertexType := PieceState 8 3
abbrev EdgeType := PieceState 12 2

instance Rubiks2x2Group : Group VertexType := PieceGroup 8 3
instance RubiksSuperGroup : Group (VertexType × EdgeType) := Prod.instGroup

section widget

inductive Color : Type | white | green | red | blue | orange | yellow

instance : ToString Color where
  toString :=
  fun c => match c with
    | Color.white => "#ffffff"
    | Color.green => "#00ff00"
    | Color.red => "#ff0000"
    | Color.blue => "#0000ff"
    | Color.orange => "#ff7f00"
    | Color.yellow => "#ffff00"

end widget
