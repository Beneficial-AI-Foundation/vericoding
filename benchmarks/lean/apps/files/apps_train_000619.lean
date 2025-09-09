-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

def count_substring_appearances (n: Nat) (strings: List String) : List Nat :=
  sorry

theorem count_substring_output_length {n: Nat} {strings: List String} :
  strings ≠ [] →
  List.length (count_substring_appearances n strings) = List.length strings :=
  sorry

theorem count_substring_long_string_zero {n: Nat} {s: String} {strings: List String} :  
  String.length s > n →
  s ∈ strings → 
  ∃ i, i < List.length strings ∧ 
    (List.get! (count_substring_appearances n strings) i) = 0 :=
  sorry

theorem count_substring_empty_list {n: Nat} : 
  count_substring_appearances n [] = [] :=
  sorry

theorem count_substring_min_n :
  count_substring_appearances 1 ["a"] = [1] ∧
  count_substring_appearances 1 ["aa"] = [0] :=
  sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval count_substring_appearances 2 ["aa"]

/-
info: [52]
-/
-- #guard_msgs in
-- #eval count_substring_appearances 2 ["d"]

/-
info: [443568031, 71288256, 41317270]
-/
-- #guard_msgs in
-- #eval count_substring_appearances 12 ["cdmn", "qweewef", "qs"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible