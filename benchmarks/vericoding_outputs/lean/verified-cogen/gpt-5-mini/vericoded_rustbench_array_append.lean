import Mathlib
-- <vc-preamble>
@[reducible, simp]
def arrayAppend_precond (a : Array Int) (b : Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper imports/opens for array lemmas used by tactics
open Std

-- </vc-helpers>

-- <vc-definitions>
def arrayAppend (a : Array Int) (b : Int) (h_precond : arrayAppend_precond (a) (b)) : Array Int :=
  a.push b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arrayAppend_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : arrayAppend_precond (a) (b)) :=
  result.size = a.size + 1 ∧ (∀ i, i < result.size → (if i < a.size then result[i]! = a[i]! else result[i]! = b))

theorem arrayAppend_spec_satisfied (a: Array Int) (b: Int) (h_precond : arrayAppend_precond (a) (b)) :
    arrayAppend_postcond (a) (b) (arrayAppend (a) (b) h_precond) h_precond := by
  dsimp [arrayAppend]
  grind
-- </vc-theorems>
