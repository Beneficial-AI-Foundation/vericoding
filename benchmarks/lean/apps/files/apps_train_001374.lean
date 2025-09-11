-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_fenwick_accesses (l1 l2 l3: String) (n: Nat) : Nat := sorry

def is_valid_binary (s: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_fenwick_result_nonnegative (l1 l2 l3: String) (n: Nat) :
  count_fenwick_accesses l1 l2 l3 n ≥ 0 := sorry

theorem count_fenwick_valid_input (l1 l2 l3: String) (n: Nat) :
  is_valid_binary l1 ∧ is_valid_binary l2 ∧ is_valid_binary l3 := sorry

theorem count_fenwick_result_bounded (l1 l2 l3: String) (n: Nat) :
  count_fenwick_accesses l1 l2 l3 n ≤ l1.length + n * l2.length + l3.length := sorry

theorem count_fenwick_deterministic (l1 l2 l3: String) (n: Nat) :
  count_fenwick_accesses l1 l2 l3 n = count_fenwick_accesses l1 l2 l3 n := sorry

theorem count_fenwick_all_zeros (n: Nat) :
  count_fenwick_accesses "0" "0" "0" n = 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_fenwick_accesses "001" "100" "011" 4

/-
info: 12
-/
-- #guard_msgs in
-- #eval count_fenwick_accesses "1000" "1101" "100" 3

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_fenwick_accesses "1010" "001" "101" 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded