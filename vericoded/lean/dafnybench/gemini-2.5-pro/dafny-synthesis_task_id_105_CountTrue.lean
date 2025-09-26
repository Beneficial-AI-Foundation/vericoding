import Mathlib
-- <vc-preamble>
def countTo (a : Array Bool) (n : Nat) : Int :=
if n = 0 then 0
else countTo a (n-1) + (if a[n-1]! then 1 else 0)

def CountTrue (a : Array Bool) : Int :=
countTo a a.size
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem countTo_spec (a : Array Bool) (n : Nat) :
n ≥ 0 ∧ n ≤ a.size →
countTo a n ≥ 0 :=
by
  induction n with
  | zero =>
    rintro ⟨_, _⟩
    simp [countTo]
  | succ k ih =>
    rintro ⟨_, h_le_succ⟩
    unfold countTo
    apply add_nonneg
    · apply ih
      constructor
      · exact Nat.zero_le k
      · exact Nat.le_of_succ_le h_le_succ
    · split_ifs <;> norm_num

theorem CountTrue_spec (a : Array Bool) :
CountTrue a = countTo a a.size :=
rfl
-- </vc-theorems>
