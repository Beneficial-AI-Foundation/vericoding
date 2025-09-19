-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_generate_permutation (n : Nat) (perm : List Nat) : Bool := sorry

theorem identity_permutation_valid (n : Nat) (h : n > 0) :
  can_generate_permutation n (List.range' 1 n) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rotated_minimum_valid {n : Nat} {perm : List Nat} 
  (h₁ : n = perm.length) 
  (h₂ : perm ≠ []) 
  (h₃ : ∀ k, k ∈ perm → k ∈ List.range' 1 n)
  (h₄ : ∀ i j, i < j → perm.get i < perm.get j → perm.get i ≤ perm.head!) :
  can_generate_permutation n perm = true := sorry

theorem specific_pattern_valid (n : Nat) (h : n ≥ 2) :
  let perm := (List.range' 2 n) ++ [1]
  can_generate_permutation n perm = true := sorry

theorem length_preserved {n : Nat} {xs : List Nat} : 
  n = xs.length → xs.length = n := sorry

theorem input_length_matches {n : Nat} {perm : List Nat} :
  can_generate_permutation n perm → perm.length = n := sorry
-- </vc-theorems>