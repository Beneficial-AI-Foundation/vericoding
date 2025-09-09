def bin (n : Nat) : String := sorry
def query_string (s : String) (n : Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def containsSubstring (s : String) (sub : String) : Bool := sorry

theorem query_string_with_all_prefixes (n : Nat) (h : 0 < n ∧ n ≤ 20) : 
  let binary_nums := String.join (List.map bin (List.range n))
  query_string binary_nums n = true
  := sorry

theorem query_string_correct (s : String) (n : Nat) (h : 0 < n ∧ n ≤ 20) :
  query_string s n = true ↔ 
    ∀ i : Nat, 1 ≤ i ∧ i ≤ n → containsSubstring s (bin i)
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval query_string "0110" 3

/-
info: False
-/
-- #guard_msgs in
-- #eval query_string "0110" 4

/-
info: True
-/
-- #guard_msgs in
-- #eval query_string "11011" 2

-- Apps difficulty: interview
-- Assurance level: unguarded