import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6_vector_Sum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6_vector_Sum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Sum of a sequence of integers -/
def sum (v : Array Int) : Int :=
  if v.size = 0 then 0
  else if v.size = 1 then v.get ⟨0⟩
  else v.get ⟨0⟩ + sum (v.extract 1 v.size)

/-- Reverse of a sequence -/
def reverse {T : Type} (s : Array T) : Array T :=
  if s.size = 0 then Array.empty
  else reverse (s.extract 1 s.size).append (Array.mk )

/-- Convert sequence to set -/
def seq2set {T : Type} (s : Array T) : List T :=
  if s.size = 0 then 
  else s.get ⟨0⟩ :: seq2set (s.extract 1 s.size)

/-- Scalar product of two integer vectors -/
def scalar_product (v1 v2 : Array Int) : Int :=
  if v1.size = 0 then 0 
  else v1.get ⟨0⟩ * v2.get ⟨0⟩ + scalar_product (v1.extract 1 v1.size) (v2.extract 1 v2.size)

theorem scalar_product_spec (v1 v2 : Array Int) :
  v1.size = v2.size → scalar_product v1 v2 = scalar_product v1 v2 := sorry

/-- Vector sum method specification -/
def vector_Sum (v : Array Int) : Int := sorry

theorem vector_Sum_spec (v : Array Int) (x : Int) :
  vector_Sum v = sum v := sorry

end DafnyBenchmarks