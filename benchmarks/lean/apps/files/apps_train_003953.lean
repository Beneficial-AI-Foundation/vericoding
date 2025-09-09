-- <vc-helpers>
-- </vc-helpers>

def string_hash (s : String) : Int :=
  sorry

theorem string_hash_returns_integer (s : String) (h : s.length > 0) :
  ∃ n : Int, string_hash s = n :=
  sorry

theorem string_hash_deterministic (s : String) (h : s.length > 1) :
  string_hash s = string_hash s :=
  sorry

theorem string_hash_space_sensitive (s : String) (h : s.length > 0) :
  string_hash s ≠ string_hash (s ++ " ") ∧
  string_hash (s ++ " ") = string_hash (s ++ " ") :=
  sorry

theorem string_hash_specific_value : 
  string_hash "a" = 64 :=
  sorry

/-
info: 64
-/
-- #guard_msgs in
-- #eval string_hash "a"

/-
info: -820
-/
-- #guard_msgs in
-- #eval string_hash "ca"

/-
info: 1120
-/
-- #guard_msgs in
-- #eval string_hash "global hash"

-- Apps difficulty: introductory
-- Assurance level: unguarded