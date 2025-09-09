-- <vc-helpers>
-- </vc-helpers>

def check_xor_sequence (n : Nat) (seq : List Nat) : String := sorry

theorem large_sequences_return_yes 
  (n : Nat) (seq : List Nat) 
  (h1 : n ≥ 68) 
  (h2 : seq.length = n) : 
  check_xor_sequence n seq = "Yes" := sorry

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

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 5 [1, 0, 2, 3, 7]

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 4 [1, 2, 3, 4]

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 68 [1] * 68

-- Apps difficulty: interview
-- Assurance level: unguarded