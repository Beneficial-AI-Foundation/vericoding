-- <vc-preamble>
def IsUpperCase (c : Char) : Bool :=
65 ≤ c.toNat ∧ c.toNat ≤ 90
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountUppercase (s : String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountUppercase_spec (s : String) :
let count := CountUppercase s
count ≥ 0 ∧
count = (s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length
:=
sorry
-- </vc-theorems>