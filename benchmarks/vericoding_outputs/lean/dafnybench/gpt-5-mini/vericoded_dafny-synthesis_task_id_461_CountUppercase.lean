import Mathlib
-- <vc-preamble>
def IsUpperCase (c : Char) : Bool :=
65 ≤ c.toNat ∧ c.toNat ≤ 90
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def uppercaseIf (c : Char) : Option Char :=
  if IsUpperCase c then some c else none

-- LLM HELPER
@[simp] theorem uppercaseIf_eq_filterMap (c : Char) :
  uppercaseIf c = (if IsUpperCase c then some c else none) := by
  simp [uppercaseIf]
-- </vc-helpers>

-- <vc-definitions>
def CountUppercase (s : String) : Int :=
Int.ofNat ((s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length)
-- </vc-definitions>

-- <vc-theorems>
theorem CountUppercase_spec (s : String) :
let count := CountUppercase s
count ≥ 0 ∧
count = (s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length
:=
by
  dsimp [CountUppercase]
  let lst := s.toList.filterMap (fun c => if IsUpperCase c then some c else none)
  constructor
  · exact Int.ofNat_nonneg (lst.length)
  · rfl
-- </vc-theorems>
