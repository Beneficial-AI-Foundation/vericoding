-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def center {n : Nat} (input : Vector String n) (width : Nat) : Vector String n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem center_spec {n : Nat} (input : Vector String n) (width : Nat)
  (h : ∀ i : Fin n, input[i].length ≥ 1) :
  let res := center input width
  (res.toList.length = n) ∧
  (∀ i : Fin n, if input[i].length > width then res[i].length = input[i].length else res[i].length = width) ∧
  (∀ i : Fin n, if input[i].length < width then
    let startPos := (width - input[i].length + 1) / 2
    let endPos := startPos + input[i].length - 1
    res[i].toList.drop startPos |>.take input[i].length = input[i].toList else True) :=
sorry
-- </vc-theorems>