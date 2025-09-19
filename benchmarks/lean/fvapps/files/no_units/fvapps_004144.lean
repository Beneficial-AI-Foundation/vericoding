-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat := sorry

def combinations (xs : List α) (k : Nat) : List (List α) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit (n : Nat) (h : n ≤ 9) :
  digits n = [] := sorry

theorem two_digits (n : Nat) (h₁ : n ≥ 10) (h₂ : n ≤ 99) :
  let result := digits n
  result.length = 1 ∧ 
  result.head! = ((toString n).toList.map (fun c => c.toNat - '0'.toNat)).foldl (·+·) 0 := sorry
-- </vc-theorems>