import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (k : Int) (w : List Int) : Prop :=
  k > 0 ∧ n ≥ 0 ∧ w.length = n ∧ ∀ i, 0 ≤ i ∧ i < w.length → w[i]! ≥ 0

def sum_trips (w : List Int) (k : Int) : Int :=
  match w with
  | [] => 0
  | head :: tail => (head + k - 1) / k + sum_trips tail k
termination_by w.length

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (w : List Int) : Prop :=
  ValidInput n k w
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: sum_trips is non-negative
lemma sum_trips_nonneg (w : List Int) (k : Int) (hk : k > 0) 
    (hw : ∀ i, 0 ≤ i ∧ i < w.length → w[i]! ≥ 0) : sum_trips w k ≥ 0 := by
  induction w with
  | nil => simp [sum_trips]
  | cons head tail ih =>
    simp [sum_trips]
    apply Int.add_nonneg
    · -- Show (head + k - 1) / k ≥ 0
      apply Int.ediv_nonneg
      · -- Show head + k - 1 ≥ 0, i.e., head + k ≥ 1
        have h_head : head ≥ 0 := by
          have h_access : (head :: tail)[0]! = head := by simp
          rw [← h_access]
          apply hw 0
          constructor
          · norm_num
          · simp
        linarith [h_head, hk]
      · linarith [hk]
    · apply ih
      intro i hi
      have h_access : (head :: tail)[i + 1]! = tail[i]! := by simp
      rw [← h_access]
      apply hw (i + 1)
      constructor
      · linarith [hi.1]
      · simp; linarith [hi.2]
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (w : List Int) (h_precond : solve_precond n k w) : Int :=
  (sum_trips w k + 1) / 2
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (w : List Int) (result : Int) (h_precond : solve_precond n k w) : Prop :=
  result ≥ 0 ∧ result = (sum_trips w k + 1) / 2

theorem solve_spec_satisfied (n : Int) (k : Int) (w : List Int) (h_precond : solve_precond n k w) :
    solve_postcond n k w (solve n k w h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- result ≥ 0
    apply Int.ediv_nonneg
    · apply Int.add_nonneg
      · apply sum_trips_nonneg
        · exact h_precond.1
        · exact h_precond.2.2.2
      · norm_num
    · norm_num
  · -- result = (sum_trips w k + 1) / 2
    rfl
-- </vc-theorems>
