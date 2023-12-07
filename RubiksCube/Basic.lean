import Lean
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

def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
  fun a b => {
    permute := b.permute * a.permute
    orient := Vector.map₂ Fin.add (permuteVector b.permute a.orient) b.orient
  }

-- variable {p o : ℕ+}

-- instance: Mul (PieceState p o) := mul
--? How can I deFine multiplication, one, and inverses as implicit components of the PieceState type?

lemma ps_mul_assoc {p o : ℕ+} : ∀ (a b c : PieceState p o), ps_mul (ps_mul a b) c = ps_mul a (ps_mul b  c) := by
  intro a b c
  simp [ps_mul]
  apply And.intro
  { simp [Perm.mul_def, Equiv.trans_assoc] }
  { simp [permuteVector]
    sorry }

lemma ps_one_mul {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul {permute := 1, orient := Vector.replicate p 0} a = a := by
  intro a
  simp [ps_mul, permuteVector]
  cases a with
  | mk a.permute a.orient =>
    simp
    sorry

lemma ps_mul_one {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul a {permute := 1, orient := Vector.replicate p 0} = a := by
  intro a
  simp [ps_mul, permuteVector]
  cases a with
  | mk a.permute a.orient =>
    simp
    sorry

def ps_inv {p o : ℕ+} : PieceState p o → PieceState p o :=
  fun ps =>
  { permute := ps.permute⁻¹
    orient := permuteVector ps.permute⁻¹ (Vector.map (fun x => -x) ps.orient) }

lemma ps_mul_left_inv {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul (ps_inv a) a = {permute := 1, orient := Vector.replicate p 0} := by
  intro a
  simp [ps_inv, ps_mul, permuteVector]
  sorry

instance PieceGroup (pieces orientations: ℕ+) :
Group (PieceState pieces orientations) := {
  mul := ps_mul
  mul_assoc := ps_mul_assoc
  one := {permute := 1, orient := Vector.replicate pieces 0}
  one_mul := ps_one_mul
  mul_one := ps_mul_one
  inv := ps_inv
  mul_left_inv := ps_mul_left_inv
}

abbrev VertexType := PieceState 8 3
abbrev EdgeType := PieceState 12 2

instance Rubiks2x2Group : Group VertexType := PieceGroup 8 3

abbrev RubiksSuperType := VertexType × EdgeType
instance RubiksSuperGroup : Group RubiksSuperType := Prod.instGroup

def solved : RubiksSuperType := 1

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

def List.vec {α : Type} : Π a : List α, Vector α (a.length)
  | [] => Vector.nil
  | (x :: xs) => Vector.cons x (xs.vec)

def corner_map : Vector (Vector Color 3) 8 :=
[
  [Color.white, Color.orange, Color.blue].vec,
  [Color.white, Color.blue, Color.red].vec,
  [Color.white, Color.red, Color.green].vec,
  [Color.white, Color.green, Color.orange].vec,
  [Color.yellow, Color.orange, Color.green].vec,
  [Color.yellow, Color.green, Color.red].vec,
  [Color.yellow, Color.red, Color.blue].vec,
  [Color.yellow, Color.blue, Color.orange].vec
].vec

def edge_map : Vector (Vector Color 2) 12 :=
[
  [Color.white, Color.blue].vec,
  [Color.white, Color.red].vec,
  [Color.white, Color.green].vec,
  [Color.white, Color.orange].vec,
  [Color.yellow, Color.green].vec,
  [Color.yellow, Color.red].vec,
  [Color.yellow, Color.blue].vec,
  [Color.yellow, Color.orange].vec,
  [Color.blue, Color.orange].vec,
  [Color.blue, Color.red].vec,
  [Color.green, Color.red].vec,
  [Color.green, Color.orange].vec
].vec

def corner_sticker : Fin 8 → Fin 3 → RubiksSuperType → Color :=
  fun i o cube => (corner_map.get (cube.1.permute⁻¹ i)).get (Fin.sub o (cube.1.orient.get i))

def edge_sticker : Fin 12 → Fin 2 → RubiksSuperType → Color :=
  fun i o cube => (edge_map.get (cube.2.permute⁻¹ i)).get (Fin.sub o (cube.2.orient.get i))

open Lean Widget

def L8x3 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 8)) ++ (List.map (fun x => (x, 1)) (List.range 8)) ++ (List.map (fun x => (x, 2)) (List.range 8))
def L12x2 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 12)) ++ (List.map (fun x => (x, 1)) (List.range 12))

#check Json.str

def cubeStickerJson : RubiksSuperType → Json :=
  fun cube => Json.mkObj
  ((List.map (fun p => (s!"c_{p.fst}_{p.snd}", Json.str (toString (corner_sticker p.fst p.snd $ cube)))) L8x3)
  ++
  (List.map (fun p => (s!"e_{p.fst}_{p.snd}", Json.str (toString (edge_sticker p.fst p.snd $ cube)))) L12x2))

@[widget] def cubeWidget : UserWidgetDefinition where
  name := "Cube State"
  javascript :="
    import * as React from 'react';

  export default function (props) {
    return React.createElement(
      'div',
      {
        style: {
          display: 'grid',
          gridTemplateColumns: 'repeat(12, 20px)',
          gridTemplateRows: 'repeat(9, 20px)',
          rowGap: '2px',
          columnGap: '2px',
          margin: '10px',
        },
      },
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '1', backgroundColor: props.c_0_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '1', backgroundColor: props.e_0_0}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '1', backgroundColor: props.c_1_0}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '2', backgroundColor: props.e_3_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '2', backgroundColor: '#ffffff'}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '2', backgroundColor: props.e_1_0}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '3', backgroundColor: props.c_3_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '3', backgroundColor: props.e_2_0}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '3', backgroundColor: props.c_2_0}}),
      React.createElement('div', {style: {gridColumn: '1',   gridRow: '4', backgroundColor: props.c_0_1}}),
      React.createElement('div', {style: {gridColumn: '2',   gridRow: '4', backgroundColor: props.e_3_1}}),
      React.createElement('div', {style: {gridColumn: '3',   gridRow: '4', backgroundColor: props.c_3_2}}),
      React.createElement('div', {style: {gridColumn: '1',   gridRow: '5', backgroundColor: props.e_8_1}}),
      React.createElement('div', {style: {gridColumn: '2',   gridRow: '5', backgroundColor: '#ff7f00'}}),
      React.createElement('div', {style: {gridColumn: '3',   gridRow: '5', backgroundColor: props.e_11_1}}),
      React.createElement('div', {style: {gridColumn: '1',   gridRow: '6', backgroundColor: props.c_7_2}}),
      React.createElement('div', {style: {gridColumn: '2',   gridRow: '6', backgroundColor: props.e_7_1}}),
      React.createElement('div', {style: {gridColumn: '3',   gridRow: '6', backgroundColor: props.c_4_1}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '4', backgroundColor: props.c_3_1}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '4', backgroundColor: props.e_2_1}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '4', backgroundColor: props.c_2_2}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '5', backgroundColor: props.e_11_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '5', backgroundColor: '#00ff00'}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '5', backgroundColor: props.e_10_0}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '6', backgroundColor: props.c_4_2}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '6', backgroundColor: props.e_4_1}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '6', backgroundColor: props.c_5_1}}),
      React.createElement('div', {style: {gridColumn: '7',   gridRow: '4', backgroundColor: props.c_2_1}}),
      React.createElement('div', {style: {gridColumn: '8',   gridRow: '4', backgroundColor: props.e_1_1}}),
      React.createElement('div', {style: {gridColumn: '9',   gridRow: '4', backgroundColor: props.c_1_2}}),
      React.createElement('div', {style: {gridColumn: '7',   gridRow: '5', backgroundColor: props.e_10_1}}),
      React.createElement('div', {style: {gridColumn: '8',   gridRow: '5', backgroundColor: '#ff0000'}}),
      React.createElement('div', {style: {gridColumn: '9',   gridRow: '5', backgroundColor: props.e_9_1}}),
      React.createElement('div', {style: {gridColumn: '7',   gridRow: '6', backgroundColor: props.c_5_2}}),
      React.createElement('div', {style: {gridColumn: '8',   gridRow: '6', backgroundColor: props.e_5_1}}),
      React.createElement('div', {style: {gridColumn: '9',   gridRow: '6', backgroundColor: props.c_6_1}}),
      React.createElement('div', {style: {gridColumn: '10',  gridRow: '4', backgroundColor: props.c_1_1}}),
      React.createElement('div', {style: {gridColumn: '11',  gridRow: '4', backgroundColor: props.e_0_1}}),
      React.createElement('div', {style: {gridColumn: '12',  gridRow: '4', backgroundColor: props.c_0_2}}),
      React.createElement('div', {style: {gridColumn: '10',  gridRow: '5', backgroundColor: props.e_9_0}}),
      React.createElement('div', {style: {gridColumn: '11',  gridRow: '5', backgroundColor: '#0000ff'}}),
      React.createElement('div', {style: {gridColumn: '12',  gridRow: '5', backgroundColor: props.e_8_0}}),
      React.createElement('div', {style: {gridColumn: '10',  gridRow: '6', backgroundColor: props.c_6_2}}),
      React.createElement('div', {style: {gridColumn: '11',  gridRow: '6', backgroundColor: props.e_6_1}}),
      React.createElement('div', {style: {gridColumn: '12',  gridRow: '6', backgroundColor: props.c_7_1}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '7', backgroundColor: props.c_4_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '7', backgroundColor: props.e_4_0}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '7', backgroundColor: props.c_5_0}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '8', backgroundColor: props.e_7_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '8', backgroundColor: '#ffff00'}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '8', backgroundColor: props.e_5_0}}),
      React.createElement('div', {style: {gridColumn: '4',   gridRow: '9', backgroundColor: props.c_7_0}}),
      React.createElement('div', {style: {gridColumn: '5',   gridRow: '9', backgroundColor: props.e_6_0}}),
      React.createElement('div', {style: {gridColumn: '6',   gridRow: '9', backgroundColor: props.c_6_0}}),
    );
  }"

#widget cubeWidget (cubeStickerJson solved)

end widget
