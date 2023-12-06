import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

def gp12 : Group (Equiv.Perm (Fin 12)) := permGroup
#check gp12

def iden : (Fin 12) → (Fin 12) := fun x => x

def idenPerm : Equiv.Perm (Fin 12) := {
  toFun := iden
  invFun := iden
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
}
