-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add (s1 s2 : String) : Nat := sorry

theorem add_commutative (s1 s2 : String) :
  add s1 s2 = add s2 s1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_identity (s : String) :
  add s "" = add "" s := sorry

theorem add_associative (s1 s2 s3 : String) :
  add (s1 ++ s2) s3 = add s1 (s2 ++ s3) := sorry

theorem add_positive (s1 s2 : String) :
  add s1 s2 ≥ 0 := sorry
-- </vc-theorems>