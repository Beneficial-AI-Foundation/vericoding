import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = '+' ∨ s.data[i]! = '-'

def computeResultHelper (s : String) (i : Nat) (cur : Int) (pm : Int) (ans : Int) : Int :=
  if h : i < s.length then
    if s.data[i]! = '+' then
      computeResultHelper s (i + 1) (cur + 1) pm ans
    else
      let newCur := cur - 1
      if newCur < pm then
        computeResultHelper s (i + 1) newCur newCur (ans + Int.ofNat i + 1)
      else
        computeResultHelper s (i + 1) newCur pm ans
  else ans
termination_by s.length - i

def computeResult (s : String) : Int :=
  computeResultHelper s 0 0 0 (Int.ofNat s.length)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma showing computeResultHelper preserves lower bound on answer
lemma computeResultHelper_ge_ans (s : String) (i : Nat) (cur : Int) (pm : Int) (ans : Int) :
    computeResultHelper s i cur pm ans ≥ ans := by
  unfold computeResultHelper
  if h : i < s.length then
    rw [dif_pos h]
    if h_plus : s.data[i]! = '+' then
      rw [if_pos h_plus]
      apply computeResultHelper_ge_ans
    else
      rw [if_neg h_plus]
      let newCur := cur - 1
      if h_lt : newCur < pm then
        rw [if_pos h_lt]
        have h_pos : Int.ofNat i + 1 > 0 := by simp
        have h_increase : ans + Int.ofNat i + 1 ≥ ans := by linarith
        have h_rec := computeResultHelper_ge_ans s (i + 1) newCur newCur (ans + Int.ofNat i + 1)
        linarith [h_rec, h_increase]
      else
        rw [if_neg h_lt]
        apply computeResultHelper_ge_ans
  else
    rw [dif_neg h]
termination_by s.length - i
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  computeResult s
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  result ≥ Int.ofNat s.length ∧ result = computeResult s

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- result ≥ Int.ofNat s.length
    unfold computeResult
    apply computeResultHelper_ge_ans
  · -- result = computeResult s  
    rfl
-- </vc-theorems>
