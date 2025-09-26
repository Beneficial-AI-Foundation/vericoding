-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_xor_sequence (n : Nat) (seq : List Nat) : String := sorry

theorem large_sequences_return_yes 
  (n : Nat) (seq : List Nat) 
  (h1 : n ≥ 68) 
  (h2 : seq.length = n) : 
  check_xor_sequence n seq = "Yes" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_sequences_return_no
  (n : Nat) (seq : List Nat)
  (h1 : n ≤ 67)
  (h2 : seq.length ≤ 1) :
  check_xor_sequence n seq = "No" := sorry

theorem permutation_invariant
  (n : Nat) (seq : List Nat)
  (h1 : 2 ≤ n) (h2 : n ≤ 67)
  (h3 : 2 ≤ seq.length) (h4 : seq.length ≤ 67) :
  check_xor_sequence n seq = check_xor_sequence n seq.reverse := sorry

theorem xor_pattern_valid 
  (n : Nat) (base : Nat)
  (h1 : 4 ≤ n) (h2 : n ≤ 67)
  (seq : List Nat)
  (h3 : seq = [base, base^^^1, base^^^2, base^^^3] ++ List.replicate (n-4) 0) :
  check_xor_sequence n seq = "Yes" := sorry
-- </vc-theorems>