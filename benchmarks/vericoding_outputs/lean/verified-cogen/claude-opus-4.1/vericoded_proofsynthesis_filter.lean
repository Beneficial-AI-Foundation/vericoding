import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun4_precond (x : Array UInt64) (y : Array UInt64) :=
  y.size = 0
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed since Array.toList_filter already exists in Mathlib
-- </vc-helpers>

-- <vc-definitions>
def myfun4 (x : Array UInt64) (y : Array UInt64) (h_precond : myfun4_precond (x) (y)) : Array UInt64 :=
  x.filter (fun k => k % 3 = 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun4_postcond (x : Array UInt64) (y : Array UInt64) (result: Array UInt64) (h_precond : myfun4_precond (x) (y)) :=
  result.toList = x.toList.filter (fun k => k % 3 = 0)

theorem myfun4_spec_satisfied (x: Array UInt64) (y: Array UInt64) (h_precond : myfun4_precond (x) (y)) :
    myfun4_postcond (x) (y) (myfun4 (x) (y) h_precond) h_precond := by
  simp [myfun4, myfun4_postcond]
-- </vc-theorems>

def main : IO Unit := return ()