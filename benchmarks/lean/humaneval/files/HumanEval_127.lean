/- 
function_signature: "def intersection(interval1: Tuple[Int, Int], interval2: Tuple[Int, Int]) -> str"
docstring: |
    You are given two intervals,
    where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
    The given intervals are closed which means that the interval (start, end)
    includes both start and end.
    For each given interval, it is assumed that its start is less or equal its end.
    Your task is to determine whether the length of intersection of these two
    intervals is a prime number.
    Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
    which its length is 1, which not a prime number.
    If the length of the intersection is a prime number, return "YES",
    otherwise, return "NO".
    If the two intervals don't intersect, return "NO".
test_cases:
  - input: [(1, 2), (2, 3)]
    expected_output: "NO"
  - input: [(-1, 1), (0, 4)]
    expected_output: "NO"
  - input: [(-3, -1), (-5, 5)]
    expected_output: "YES"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (interval1: Int × Int) (interval2: Int × Int) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Int × Int → Int × Int → String)
-- inputs
(interval1: Int × Int)
(interval2: Int × Int) :=
-- spec
let spec (result: String) :=
let (s1, e1) := interval1;
let (s2, e2) := interval2;
s1 ≤ e1 → s2 ≤ e2 →
let intersectionStart := max s1 s2;
let intersectionEnd := min e1 e2;
let hasIntersection := intersectionStart ≤ intersectionEnd;
let isPrime := Nat.Prime (intersectionEnd - intersectionStart).toNat;
(result = "YES" ↔ hasIntersection ∧ isPrime) ∧
(result = "NO" ↔ ¬hasIntersection ∨ ¬isPrime) ∧
(result = "YES" ∨ result = "NO")
-- program terminates
∃ result, impl interval1 interval2 = result ∧
-- return value satisfies spec
spec result

theorem correctness
(interval1: Int × Int)
(interval2: Int × Int)
: problem_spec implementation interval1 interval2 :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation (1, 2) (2, 3) = "NO"
-- #test implementation (-1, 1) (0, 4) = "NO"
-- #test implementation (-3, -1) (-5, 5) = "YES"