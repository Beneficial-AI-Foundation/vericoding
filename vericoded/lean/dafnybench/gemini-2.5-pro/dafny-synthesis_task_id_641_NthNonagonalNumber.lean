import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
Shows that for any integer `n`, the expression `n * (7 * n - 5)` is even.
This is a helper lemma to justify the integer division by 2 in the definition
of nonagonal numbers.
-/
lemma n_mul_seven_n_minus_five_is_even (n : Int) : Even (n * (7 * n - 5)) := by
  cases Int.even_or_odd n with
  | inl h_even =>
    rcases h_even with ⟨k, rfl⟩
    use k * (14 * k - 5)
    ring
  | inr h_odd =>
    rcases h_odd with ⟨k, rfl⟩
    use (2 * k + 1) * (7 * k + 1)
    ring
-- </vc-helpers>

-- <vc-definitions>
def NthNonagonalNumber (n : Int) : Int :=
if n ≥ 0 then n * (7 * n - 5) / 2 else 0
-- </vc-definitions>

-- <vc-theorems>
theorem NthNonagonalNumber_spec (n : Int) :
n ≥ 0 → NthNonagonalNumber n = n * (7 * n - 5) / 2 :=
by
  intro h
  simp [NthNonagonalNumber, h]
-- </vc-theorems>
