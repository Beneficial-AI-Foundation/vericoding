import Mathlib
-- <vc-preamble>
def sum (s : Array Int) (n : Nat) : Int :=
if s.size = 0 ∨ n = 0 then
0
else
s[0]! + sum (s.extract 1 s.size) (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic properties of sum function
lemma sum_zero (s : Array Int) : sum s 0 = 0 := by simp [sum]

lemma sum_empty (n : Nat) : sum #[] n = 0 := by simp [sum]
-- </vc-helpers>

-- <vc-definitions>
def below_zero (ops : Array Int) : Bool :=
(List.range (ops.size + 1)).any (fun n => sum ops n < 0)
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) (n : Nat) :
n ≤ s.size → sum s n = sum s n :=
fun _ => rfl

theorem below_zero_spec (ops : Array Int) :
below_zero ops = true ↔ ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 :=
by
  unfold below_zero
  simp [List.any_eq_true, List.mem_range, Nat.lt_succ_iff]
-- </vc-theorems>
