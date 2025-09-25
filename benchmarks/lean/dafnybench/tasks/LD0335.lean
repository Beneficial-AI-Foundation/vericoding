-- <vc-preamble>
def power (x : Float) (n : Nat) : Float :=
match n with
| 0 => 1.0
| n + 1 => x * power x n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerIter (x : Float) (n : Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powerIter_spec (x : Float) (n : Nat) :
powerIter x n = power x n :=
sorry
-- </vc-theorems>