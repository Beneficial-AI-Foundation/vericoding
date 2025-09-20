-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_dup (arr : List Nat) : Nat := sorry

theorem find_dup_correct (n : Nat) (duplicate : Nat) 
  (h1 : n ≥ 2)
  (h2 : duplicate < n)
  (h3 : duplicate > 0)
  (arr : List Nat)
  (h4 : arr = (List.range (n-1)).append [duplicate]) :
  find_dup arr = duplicate ∧ 
  (arr.filter (λ x => x = duplicate)).length = 2 ∧
  ∀ x ∈ arr, x ≤ n-1 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>