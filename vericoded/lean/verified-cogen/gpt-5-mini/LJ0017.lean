import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun4_precond (x : Array UInt64) (y : Array UInt64) :=
  y.size = 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- LLM HELPER
namespace LLMHelpers

-- LLM HELPER
@[inline]
def list_to_array {α : Type} (l : List α) : Array α := l.toArray

-- LLM HELPER
theorem list_to_array_to_list {α : Type} (l : List α) : (list_to_array l).toList = l := by
  induction l with
  | nil => simp [list_to_array]
  | cons hd tl ih => simp [list_to_array, ih]

end LLMHelpers
-- </vc-helpers>

-- <vc-definitions>
def myfun4 (x : Array UInt64) (y : Array UInt64) (h_precond : myfun4_precond (x) (y)) : Array UInt64 :=
  LLMHelpers.list_to_array (x.toList.filter fun k => k % 3 = 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun4_postcond (x : Array UInt64) (y : Array UInt64) (result: Array UInt64) (h_precond : myfun4_precond (x) (y)) :=
  result.toList = x.toList.filter (fun k => k % 3 = 0)

theorem myfun4_spec_satisfied (x: Array UInt64) (y: Array UInt64) (h_precond : myfun4_precond (x) (y)) :
    myfun4_postcond (x) (y) (myfun4 (x) (y) h_precond) h_precond := by
  dsimp [myfun4, myfun4_postcond]
  exact LLMHelpers.list_to_array_to_list (x.toList.filter fun k => k % 3 = 0)
-- </vc-theorems>
