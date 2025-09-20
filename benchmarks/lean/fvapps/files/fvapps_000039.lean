-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_start_point (cost1: Nat) (cost2: Nat) (cost3: Nat) (str: String) : Nat := sorry

-- Single character string theorems
-- </vc-definitions>

-- <vc-theorems>
theorem single_A_start_point (c: Nat) :
  c > 0 → find_min_start_point c c c "A" = (1 : Nat) := sorry

theorem single_B_start_point (c: Nat) :
  c > 0 → find_min_start_point c c c "B" = (1 : Nat) := sorry

-- Example case theorems

theorem two_B_start_point :
  find_min_start_point (2 : Nat) (2 : Nat) (1 : Nat) "BB" = (2 : Nat) := sorry

theorem AB_start_point :
  find_min_start_point (1 : Nat) (1 : Nat) (1 : Nat) "AB" = (1 : Nat) := sorry

theorem long_string_start_point :
  find_min_start_point (3 : Nat) (2 : Nat) (8 : Nat) "AABBBBAABB" = (3 : Nat) := sorry
-- </vc-theorems>