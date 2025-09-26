import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun4_precond (x : Array UInt64) (y : Array UInt64) : Prop :=
  y.size = 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem array_toList_mk {α} (l : List α) : (Array.mk l).toList = l := rfl
-- </vc-helpers>

-- <vc-definitions>
def myfun4 (x : Array UInt64) (y : Array UInt64) (h_precond : myfun4_precond x y) : Array UInt64 :=
  Array.mk (x.toList.filter (fun k => k % 3 = 0))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun4_postcond (x : Array UInt64) (y_old : Array UInt64) (result : Array UInt64) (h_precond : myfun4_precond x y_old) : Prop :=
  result.toList = x.toList.filter (fun k => k % 3 = 0)

theorem myfun4_spec_satisfied (x : Array UInt64) (y : Array UInt64) (h_precond : myfun4_precond x y) :
    myfun4_postcond x y (myfun4 x y h_precond) h_precond := by
  simp [myfun4_postcond, myfun4]
-- </vc-theorems>
