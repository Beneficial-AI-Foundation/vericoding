import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def avg_of_sum (sum n : Int) : Float := Float.ofInt sum / Float.ofInt n

lemma nonzero_of_pos {n : Int} (h : n > 0) : n ≠ 0 := by linarith

lemma avg_of_sum_spec (sum n : Int) (h : n ≠ 0) : avg_of_sum sum n = Float.ofInt sum / Float.ofInt n := rfl

-- </vc-helpers>

-- <vc-definitions>
def SumAndAverage (n : Int) : Int × Float :=
if h : n > 0 then
  let sum := (n * (n + 1)) / 2
  (sum, Float.ofInt sum / Float.ofInt n)
else
  (0, 0.0)

-- </vc-definitions>

-- <vc-theorems>
theorem SumAndAverage_spec (n : Int) :
n > 0 →
let (sum, average) := SumAndAverage n
sum = n * (n + 1) / 2 ∧
average = Float.ofInt sum / Float.ofInt n  :=
by
  intro hn
  have hPair : SumAndAverage n = (n * (n + 1) / 2, Float.ofInt (n * (n + 1) / 2) / Float.ofInt n) := by
    dsimp [SumAndAverage]
    simp [if_pos hn]
  rw [hPair]
  simp

-- </vc-theorems>
