-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_singing_championship (singers : List (Int × Int)) : List Int := sorry

def make_valid_interval (a b : Int) : Int × Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_singer :
  solve_singing_championship [(1,2)] = [0] := sorry

/-
info: [4, 1, 1]
-/
-- #guard_msgs in
-- #eval solve_singing_championship [(10, 20), (13, 18), (15, 19)]

/-
info: [4, 2, 0]
-/
-- #guard_msgs in
-- #eval solve_singing_championship [(10, 22), (13, 21), (15, 20)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible