-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_permutation (N k S : Nat) (arr : List Nat) : List Nat := sorry

def is_valid_permutation (n : Nat) (perm : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_perm_valid_permutation 
  (N k S : Nat)
  (arr : List Nat)
  (h1 : N > 0)
  (h2 : k > 0) 
  (h3 : S > 0)
  (h4 : arr.length > 0) :
  is_valid_permutation N (solve_permutation N k S arr) = true := sorry

theorem solve_perm_length
  (N k S : Nat)
  (arr : List Nat)
  (h1 : N > 0)
  (h2 : k > 0)
  (h3 : S > 0)
  (h4 : arr.length > 0) :
  (solve_permutation N k S arr).length = N := sorry

theorem solve_perm_descending
  (N k S : Nat)
  (arr : List Nat) 
  (h1 : N > 0)
  (h2 : k > 0)
  (h3 : S > 0)
  (h4 : arr.length > 0) :
  ∀ i j, i < j → j < (solve_permutation N k S arr).length → 
  (solve_permutation N k S arr).get ⟨i, sorry⟩ ≥ 
  (solve_permutation N k S arr).get ⟨j, sorry⟩ := sorry

theorem solve_perm_edge_case
  (N : Nat)
  (h : N > 0) :
  solve_permutation N 1 1 (List.replicate N 1) = List.range' N N := sorry
-- </vc-theorems>