import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  4 ≤ n ∧ n ≤ 1000 ∧ 1 ≤ k ∧ k ≤ 4 ∧ k < n

partial def factorial (n : Int) : Int :=
  if n ≤ 1 then 1 else n * factorial (n - 1)

partial def derangement (n : Int) : Int :=
  if n ≤ 1 then 0
  else if n = 2 then 1
  else (n - 1) * (derangement (n - 1) + derangement (n - 2))

partial def binomial (n k : Int) : Int :=
  if k > n then 0
  else if k = 0 ∨ k = n then 1
  else factorial n / (factorial k * factorial (n - k))

partial def sum_binomial_derangement (n k i : Int) : Int :=
  if i ≥ n - k then 0
  else binomial n i * derangement (n - i) + sum_binomial_derangement n k (i + 1)

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Additional helper lemmas and definitions
-- These helpers support the main solve function and its verification

-- Helper to extract ValidInput components
lemma ValidInput.n_ge_4 {n k : Int} (h : ValidInput n k) : 4 ≤ n := h.1
lemma ValidInput.n_le_1000 {n k : Int} (h : ValidInput n k) : n ≤ 1000 := h.2.1
lemma ValidInput.k_ge_1 {n k : Int} (h : ValidInput n k) : 1 ≤ k := h.2.2.1
lemma ValidInput.k_le_4 {n k : Int} (h : ValidInput n k) : k ≤ 4 := h.2.2.2.1
lemma ValidInput.k_lt_n {n k : Int} (h : ValidInput n k) : k < n := h.2.2.2.2
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  factorial n - sum_binomial_derangement n k 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result = factorial n - sum_binomial_derangement n k 0

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve
  simp
-- </vc-theorems>
