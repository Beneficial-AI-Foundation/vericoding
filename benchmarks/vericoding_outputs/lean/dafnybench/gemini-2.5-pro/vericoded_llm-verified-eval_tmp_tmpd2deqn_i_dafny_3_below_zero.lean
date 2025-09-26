import Mathlib
-- <vc-preamble>
def sum (s : Array Int) (n : Nat) : Int :=
if s.size = 0 ∨ n = 0 then
0
else
s[0]! + sum (s.extract 1 s.size) (n-1)
-- </vc-preamble>

-- <vc-helpers>
theorem sum_zero (s : Array Int) : sum s 0 = 0 := by
  simp [sum]
-- </vc-helpers>

-- <vc-definitions>
def below_zero (ops : Array Int) : Bool :=
(List.range ops.size).any fun i => (sum ops (i + 1)) < 0
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) (n : Nat) :
n ≤ s.size → sum s n = sum s n :=
fun _ => rfl

theorem below_zero_spec (ops : Array Int) :
below_zero ops = true ↔ ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 :=
by
  simp [below_zero, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi_lt, hi_neg⟩
    use i + 1
    exact ⟨Nat.succ_le_of_lt hi_lt, hi_neg⟩
  · rintro ⟨n, hn_le, hn_neg⟩
    have hn_ne_zero : n ≠ 0 := by
      intro hn_zero
      rw [hn_zero, sum_zero] at hn_neg
      linarith
    use n - 1
    constructor
    · exact lt_of_lt_of_le (Nat.pred_lt hn_ne_zero) hn_le
    · rw [Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero))]
      exact hn_neg
-- </vc-theorems>
