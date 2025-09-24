-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Nat := sorry

theorem solve_single_wildcard : solve "aa?" = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_multi_wildcard : solve "a???" = 6 := sorry

theorem solve_all_wildcards : solve "????" = 4 := sorry
-- </vc-theorems>