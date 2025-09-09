-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : Nat := sorry

theorem solve_single_wildcard : solve "aa?" = 2 := sorry

theorem solve_multi_wildcard : solve "a???" = 6 := sorry

theorem solve_all_wildcards : solve "????" = 4 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded