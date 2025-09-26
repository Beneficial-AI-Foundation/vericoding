import Mathlib
-- <vc-preamble>
def ValidInput (diameters : List Int) : Prop :=
  diameters.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < diameters.length → diameters[i]! > 0

def num_distinct (s : List Int) : Int :=
  if s.length = 0 then 0
  else if s.head! ∈ s.tail then num_distinct s.tail
  else 1 + num_distinct s.tail
  termination_by s.length

@[reducible, simp]
def solve_precond (diameters : List Int) : Prop :=
  ValidInput diameters
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Properties of num_distinct
lemma num_distinct_nonneg (s : List Int) : 0 ≤ num_distinct s := by
  induction s with
  | nil => unfold num_distinct; norm_num
  | cons h t ih => 
    unfold num_distinct
    simp only [List.length_cons, List.head!_cons, List.tail_cons]
    by_cases h_mem : h ∈ t
    · simp [h_mem]
      exact ih
    · simp [h_mem]
      linarith

lemma num_distinct_le_length (s : List Int) : num_distinct s ≤ s.length := by
  induction s with
  | nil => unfold num_distinct; norm_num
  | cons h t ih => 
    unfold num_distinct
    simp only [List.length_cons, List.head!_cons, List.tail_cons]
    by_cases h_mem : h ∈ t
    · simp [h_mem]
      linarith [ih]
    · simp [h_mem]
      rw [add_comm 1 (num_distinct t)]
      simp [List.length_cons]
      linarith [ih]

lemma num_distinct_pos_of_nonempty (s : List Int) (h : 0 < s.length) : 1 ≤ num_distinct s := by
  cases s with
  | nil => norm_num at h
  | cons head t => 
    unfold num_distinct
    simp only [List.length_cons, List.head!_cons, List.tail_cons]
    by_cases h_mem : head ∈ t
    · simp [h_mem]
      by_cases h_t : t = []
      · subst h_t; contradiction
      · apply num_distinct_pos_of_nonempty
        rw [List.length_pos_iff_ne_nil]
        exact h_t
    · simp [h_mem]
      linarith [num_distinct_nonneg t]
-- </vc-helpers>

-- <vc-definitions>
def solve (diameters : List Int) (h_precond : solve_precond diameters) : Int :=
  num_distinct diameters
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (diameters : List Int) (result : Int) (h_precond : solve_precond diameters) : Prop :=
  result = num_distinct diameters ∧ result ≥ 1 ∧ result ≤ diameters.length

theorem solve_spec_satisfied (diameters : List Int) (h_precond : solve_precond diameters) :
    solve_postcond diameters (solve diameters h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · rfl
  constructor
  · apply num_distinct_pos_of_nonempty
    exact h_precond.1
  · exact num_distinct_le_length diameters
-- </vc-theorems>
