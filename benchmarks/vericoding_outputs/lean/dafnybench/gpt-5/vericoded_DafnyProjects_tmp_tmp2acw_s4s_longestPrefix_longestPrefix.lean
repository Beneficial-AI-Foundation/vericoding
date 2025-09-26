import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma min_lt_both_false (m n : Nat) : ¬ (Nat.min m n < m ∧ Nat.min m n < n) := by
  by_cases hmn : m ≤ n
  · have hmin : Nat.min m n = m := Nat.min_eq_left hmn
    intro h
    have hlt : m < m := by simpa [hmin] using h.left
    exact lt_irrefl _ hlt
  · have hlt : n < m := Nat.lt_of_not_ge hmn
    have hmin : Nat.min m n = n := Nat.min_eq_right (Nat.le_of_lt hlt)
    intro h
    have hlt' : n < n := by simpa [hmin] using h.right
    exact lt_irrefl _ hlt'

-- </vc-helpers>

-- <vc-definitions>
def longestPrefix (a b : Array Int) : Nat :=
Nat.min a.size b.size
-- </vc-definitions>

-- <vc-theorems>
theorem longestPrefix_spec (a b : Array Int) (i : Nat) :
let i := longestPrefix a b
i ≤ a.size ∧ i ≤ b.size ∧
(i < a.size ∧ i < b.size → a[i]! ≠ b[i]!) :=
by
  have h₁ : Nat.min a.size b.size ≤ a.size := Nat.min_le_left _ _
  have h₂ : Nat.min a.size b.size ≤ b.size := Nat.min_le_right _ _
  have h₃ :
      (Nat.min a.size b.size < a.size ∧ Nat.min a.size b.size < b.size) →
      a[Nat.min a.size b.size]! ≠ b[Nat.min a.size b.size]! :=
    by
      intro h
      have : False := (min_lt_both_false (a.size) (b.size)) (by simpa using h)
      exact this.elim
  have hP :
      Nat.min a.size b.size ≤ a.size ∧
      Nat.min a.size b.size ≤ b.size ∧
      (Nat.min a.size b.size < a.size ∧ Nat.min a.size b.size < b.size →
        a[Nat.min a.size b.size]! ≠ b[Nat.min a.size b.size]!) :=
    And.intro h₁ (And.intro h₂ h₃)
  simpa [longestPrefix] using hP

-- </vc-theorems>
