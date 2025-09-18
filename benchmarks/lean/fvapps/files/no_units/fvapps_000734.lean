-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_bouquet (mg my mr og oy or_ pg py pr : Nat) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_bouquet_all_same (n : Nat) :
  let result := find_max_bouquet n n n n n n n n n
  let expected := if 3*n % 2 = 1 then 3*n else 3*n - 1
  result = expected ∨ result = 0 :=
sorry

theorem find_max_bouquet_zeros :
  find_max_bouquet 0 0 0 0 0 0 0 0 0 = 0 :=
sorry
-- </vc-theorems>