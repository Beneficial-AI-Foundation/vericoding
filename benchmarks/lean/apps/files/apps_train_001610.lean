-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_perfect_array (n : Nat) : List Nat := sorry

def is_perfect_array (arr : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_perfect_array_length (n : Nat) (h : n > 0) :
  List.length (generate_perfect_array n) = n := sorry

theorem generate_perfect_array_elements_equal (n : Nat) (h : n > 0) :
  ∀ i j, i < n → j < n → 
    List.get! (generate_perfect_array n) i = List.get! (generate_perfect_array n) j := sorry

/-
info: [4]
-/
-- #guard_msgs in
-- #eval generate_perfect_array 1

/-
info: [4, 4]
-/
-- #guard_msgs in
-- #eval generate_perfect_array 2

/-
info: [4, 4, 4, 4]
-/
-- #guard_msgs in
-- #eval generate_perfect_array 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible