-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare_tournaments (f1 f2 r1 r2 r3 r4 : Nat) (p1 p2 p3 p4 : Float) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_tournaments_returns_valid_result
  (f1 f2 r1 r2 r3 r4 : Nat) (p1 p2 p3 p4 : Float)
  (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
  (h2 : 0 ≤ p2 ∧ p2 ≤ 1)
  (h3 : 0 ≤ p3 ∧ p3 ≤ 1) 
  (h4 : 0 ≤ p4 ∧ p4 ≤ 1) :
  (compare_tournaments f1 f2 r1 r2 r3 r4 p1 p2 p3 p4) = "FIRST" ∨
  (compare_tournaments f1 f2 r1 r2 r3 r4 p1 p2 p3 p4) = "SECOND" ∨
  (compare_tournaments f1 f2 r1 r2 r3 r4 p1 p2 p3 p4) = "BOTH" :=
sorry

theorem compare_tournaments_zero_probability (f r : Nat) :
  compare_tournaments f f r r r r 0 0 0 0 = "BOTH" :=
sorry
-- </vc-theorems>