-- <vc-helpers>
-- </vc-helpers>

def num_perms_di_sequence (s : String) : Nat := sorry

def MOD := 1000000007

theorem num_perms_di_sequence_nonneg (s : String) :
  num_perms_di_sequence s ≥ 0 := sorry 

theorem num_perms_di_sequence_within_mod (s : String) :
  num_perms_di_sequence s < MOD := sorry

theorem all_decreasing_sequence_one_perm (s : String) :
  (∀ c ∈ s.data, c = 'D') → 
  num_perms_di_sequence s = 1 := sorry

theorem all_increasing_sequence_one_perm (s : String) :
  (∀ c ∈ s.data, c = 'I') → 
  num_perms_di_sequence s = 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_perms_di_sequence "DID"

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_perms_di_sequence "D"

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_perms_di_sequence "III"

-- Apps difficulty: interview
-- Assurance level: unguarded