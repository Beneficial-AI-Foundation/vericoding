import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = n ∧ ∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 1

def Transform (a : List Int) : List Int :=
  List.range a.length |>.mapIdx (fun i _ => a[i]! - (i + 1))

def Abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def SumAbsDiffs (a : List Int) (target : Int) : Int :=
  match a with
  | [] => 0
  | h :: t => Abs (h - target) + SumAbsDiffs t target

def SortedSeq (a : List Int) : List Int :=
  a.mergeSort (· ≤ ·)

def RoundToInt (x : Int) (y : Int) : Int :=
  if y = 0 then 0
  else if x ≥ 0 then (x + y / 2) / y
  else (x - y / 2) / y

def MedianOf (a : List Int) : Int :=
  let sorted := SortedSeq a
  if sorted.length = 0 then 0
  else if sorted.length % 2 = 1 then
    sorted[sorted.length / 2]!
  else if sorted.length = 2 then
    RoundToInt (sorted[0]! + sorted[1]!) 2
  else
    RoundToInt (sorted[sorted.length / 2 - 1]! + sorted[sorted.length / 2]!) 2

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma transform_length (a : List Int) : (Transform a).length = a.length := by
  unfold Transform
  simp [List.length_mapIdx, List.length_range]

-- LLM HELPER
lemma sortedSeq_length (a : List Int) : (SortedSeq a).length = a.length := by
  unfold SortedSeq
  simp [List.length_mergeSort]

-- LLM HELPER
lemma sortedSeq_mem (a : List Int) (x : Int) : x ∈ SortedSeq a ↔ x ∈ a := by
  unfold SortedSeq
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma my_abs_nonneg (x : Int) : Abs x ≥ 0 := by
  unfold Abs
  split <;> omega

-- LLM HELPER
lemma sumAbsDiffs_nonneg (a : List Int) (target : Int) : SumAbsDiffs a target ≥ 0 := by
  induction a with
  | nil => unfold SumAbsDiffs; omega
  | cons h t ih =>
    unfold SumAbsDiffs
    have h1 := my_abs_nonneg (h - target)
    have h2 := ih
    omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  let transformed := Transform a
  let median := MedianOf transformed
  SumAbsDiffs transformed median
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  result ≥ 0 ∧ result = SumAbsDiffs (Transform a) (MedianOf (Transform a))

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- prove result ≥ 0
    apply sumAbsDiffs_nonneg
  · -- prove result equals the specification
    rfl
-- </vc-theorems>
