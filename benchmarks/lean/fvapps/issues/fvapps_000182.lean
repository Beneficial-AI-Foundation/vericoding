-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_all_codes (s : String) (k : Nat) : Bool := sorry

theorem empty_string_always_false {k : Nat} (h : k ≥ 1) :
  has_all_codes "" k = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_sequence_length_requirement {k : Nat} (h : k ≥ 1) (h2 : k ≤ 4) :
  ∀ s, s.length < 2^k + k - 1 → has_all_codes s k = false := sorry 

theorem has_all_codes_returns_bool (s : String) (k : Nat) (h : k ≥ 1) :
  has_all_codes s k = true ∨ has_all_codes s k = false := sorry

theorem complete_sequence_true {k : Nat} (h : k ≥ 1) (h2 : k ≤ 4) :
  let seq := String.mk (List.join (List.map (fun i => (toString i).data) (List.range (2^k))))
  has_all_codes (seq ++ (seq.take (k-1))) k = true := sorry

theorem substring_property (s : String) (k : Nat) (h : k ≥ 1) :
  has_all_codes s k = true →
  (has_all_codes (s ++ "0") k = true ∧ has_all_codes ("0" ++ s) k = true) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval has_all_codes "00110110" 2

/-
info: False
-/
-- #guard_msgs in
-- #eval has_all_codes "0110" 2

/-
info: True
-/
-- #guard_msgs in
-- #eval has_all_codes "0110" 1
-- </vc-theorems>