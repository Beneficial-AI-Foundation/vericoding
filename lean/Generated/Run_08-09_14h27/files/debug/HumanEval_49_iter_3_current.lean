/- 
function_signature: "def modp(n: Nat, p: Nat) -> Nat"
docstring: |
    Return 2^n modulo p (be aware of numerics).
test_cases:
  - input: [3, 5]
    expected_output: 3
  - input: [1101, 101]
    expected_output: 2
  - input: [0, 101]
    expected_output: 0
  - input: [100, 101]
    expected_output: 1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n p: Nat) : Nat :=
  if p = 0 then 0 else (Nat.pow 2 n) % p

def problem_spec
-- function signature
(implementation: Nat → Nat → Nat)
-- inputs
(n p: Nat) :=
-- spec
let spec (result: Nat) :=
0 < p ∧
result < p ∧
(∃ k : Nat, p * k + result = Nat.pow 2 n)
-- program termination
∃ result, implementation n p = result ∧
spec result

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  unfold problem_spec
  by_cases h : p = 0
  · -- Case p = 0
    simp [implementation, h]
    use 0
    simp [h]
    have : ¬(0 : Nat) < 0 := by norm_num
    exact this
  · -- Case p > 0
    have hp_pos : 0 < p := Nat.pos_of_ne_zero h
    use (Nat.pow 2 n) % p
    constructor
    · simp [implementation, h]
    constructor
    · exact hp_pos
    constructor
    · exact Nat.mod_lt (Nat.pow 2 n) hp_pos
    · use (Nat.pow 2 n) / p
      rw [Nat.mul_comm]
      have : Nat.pow 2 n % p + Nat.pow 2 n / p * p = Nat.pow 2 n := by
        rw [Nat.add_comm]
        exact Nat.div_add_mod (Nat.pow 2 n) p
      exact this

-- #test implementation 3 5 = 3
-- #test implementation 1101 101 = 2
-- #test implementation 0 101 = 1
-- #test implementation 3 11 = 8
-- #test implementation 100 101 = 1