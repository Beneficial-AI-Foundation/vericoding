-- <vc-helpers>
-- </vc-helpers>

def alpha_num_inverse (s: String) : String := sorry 

theorem pure_alpha_only_digits {s : String} 
  (h : ∀ c ∈ s.data, c ≥ 'a' ∧ c ≤ 'z') :
  ∀ c ∈ (alpha_num_inverse s).data, c ≥ '0' ∧ c ≤ '9' := sorry

theorem pure_alpha_conversion_correct {s : String}
  (h : ∀ c ∈ s.data, c ≥ 'a' ∧ c ≤ 'z') :
  alpha_num_inverse s = String.join (s.data.map (fun c => toString (c.toNat - 96))) := sorry

/-
info: '1y226'
-/
-- #guard_msgs in
-- #eval alpha_num_inverse "a25bz"

/-
info: 'r262526n'
-/
-- #guard_msgs in
-- #eval alpha_num_inverse "18zyz14"

/-
info: '1234'
-/
-- #guard_msgs in
-- #eval alpha_num_inverse "abcd"

-- Apps difficulty: introductory
-- Assurance level: unguarded