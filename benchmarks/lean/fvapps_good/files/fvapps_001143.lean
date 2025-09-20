-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_interesting_numbers (m : Nat) : List Nat := sorry 
def solve_test_case (m : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_interesting_numbers_range (m : Nat) (h : 0 < m) (h2 : m ≤ 100) : 
  ∀ x ∈ find_interesting_numbers m, 
    m < x ∧ x ≤ 2 * m := sorry

theorem find_interesting_numbers_sorted (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  List.Pairwise (· ≤ ·) (find_interesting_numbers m) := sorry

theorem solve_test_case_first_is_length (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  List.head! (solve_test_case m) = (List.length (solve_test_case m)) - 1 := sorry

theorem solve_test_case_all_elements (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  ∀ x, x ∈ solve_test_case m → x ≥ 0 := sorry

theorem interesting_numbers_property (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  ∀ a ∈ find_interesting_numbers m,
    (a * m) % (a - m) = 0 := sorry

theorem find_interesting_numbers_complete (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  ∀ a : Nat, m < a → a ≤ 2 * m → 
    (a * m) % (a - m) = 0 → 
    a ∈ find_interesting_numbers m := sorry
-- </vc-theorems>