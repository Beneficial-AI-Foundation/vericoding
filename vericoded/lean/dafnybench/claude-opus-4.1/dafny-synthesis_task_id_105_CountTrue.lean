import Mathlib
-- <vc-preamble>
def countTo (a : Array Bool) (n : Nat) : Int :=
if n = 0 then 0
else countTo a (n-1) + (if a[n-1]! then 1 else 0)

def CountTrue (a : Array Bool) : Int :=
countTo a a.size
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for proving properties about countTo
lemma countTo_nonneg (a : Array Bool) (n : Nat) : countTo a n ≥ 0 := by
  -- LLM HELPER
  induction n with
  | zero =>
    unfold countTo
    simp
  | succ n ih =>
    unfold countTo
    split
    · -- case when n + 1 = 0, which is impossible
      simp
    · -- case when n + 1 ≠ 0
      split
      · -- case when a[n]! = true
        simp only [Nat.add_sub_cancel]
        apply Int.add_nonneg
        · exact ih
        · norm_num
      · -- case when a[n]! = false  
        simp only [Nat.add_sub_cancel, add_zero]
        exact ih
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem countTo_spec (a : Array Bool) (n : Nat) :
n ≥ 0 ∧ n ≤ a.size →
countTo a n ≥ 0 :=
by
  intro ⟨h_nonneg, h_le⟩
  exact countTo_nonneg a n

theorem CountTrue_spec (a : Array Bool) :
CountTrue a = countTo a a.size :=
by
  unfold CountTrue
  rfl
-- </vc-theorems>
