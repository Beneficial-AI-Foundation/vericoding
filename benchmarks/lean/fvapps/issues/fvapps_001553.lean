-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def magic_call_depth_number (p : Program) : List Nat := sorry

theorem magic_returns_valid_range (p : Program) :
  let result := magic_call_depth_number p
  result.length = 2 ∧ 
  result.head! ≤ result.get! 1 ∧
  ∀ x ∈ result, x ≥ 0
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_proc_depth_zero (c : Char) : 
  magic_call_depth_number (Program.proc c Program.end) = [0, 0] := sorry

theorem depth_bounded_by_unique_procs (p : Program) :
  let result := magic_call_depth_number p
  let proc_count := sorry -- Helper function to count unique procedures
  result.get! 1 ≤ proc_count := sorry

theorem empty_program : 
  magic_call_depth_number Program.empty = [0, 0] := sorry

/-
info: [0, 0]
-/
-- #guard_msgs in
-- #eval magic_call_depth_number "p0F2LF2RqP0"

/-
info: [2, 3]
-/
-- #guard_msgs in
-- #eval magic_call_depth_number "p1P2P3qp2P1qp3P1qP3"

/-
info: [4, 4]
-/
-- #guard_msgs in
-- #eval magic_call_depth_number "p1P2qp2P3qp3P4qP4p4P1q"
-- </vc-theorems>