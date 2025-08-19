import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def List.mergeSort (l : List Rat) (le : Rat → Rat → Bool) : List Rat :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge (mergeSort left le) (mergeSort right le) le
where
  merge : List Rat → List Rat → (Rat → Rat → Bool) → List Rat
  | [], ys, _ => ys
  | xs, [], _ => xs
  | x :: xs, y :: ys, le =>
    if le x y then x :: merge xs (y :: ys) le
    else y :: merge (x :: xs) ys le

-- LLM HELPER
def quickselect (numbers: List Rat) (k: Nat) : Rat :=
  if h : k < numbers.length then
    let sorted := numbers.mergeSort (· ≤ ·)
    sorted.get! k
  else
    0

def implementation (numbers: List Rat) : Rat := 
  if numbers.length = 0 then 0
  else if numbers.length % 2 = 1 then
    quickselect numbers (numbers.length / 2)
  else
    let mid1 := quickselect numbers (numbers.length / 2 - 1)
    let mid2 := quickselect numbers (numbers.length / 2)
    (mid1 + mid2) / 2

-- LLM HELPER
lemma filter_le_length (l : List Rat) (p : Rat → Bool) : (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.filter]
    split_ifs with h
    · simp [Nat.add_one_le_iff]
      exact ih
    · exact Nat.le_trans ih (Nat.le_succ _)

-- LLM HELPER
lemma median_properties (numbers: List Rat) : 
  numbers.length > 0 → 
  let result := implementation numbers
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  less_eq.length + more_eq.length - (numbers.filter (fun x => x = result)).length = numbers.length := by
  intro h
  simp [implementation]
  split_ifs
  · simp
  · simp [quickselect]
    split_ifs
    · simp
    · simp
  · simp [quickselect]
    split_ifs
    · simp
    · simp
    · simp
    · simp

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h
    constructor
    · constructor
      · intro h1 h2 h3
        rfl
      · constructor
        · intro h_odd
          simp [implementation] at h_odd ⊢
          split_ifs at h_odd with h1 h2
          · contradiction
          · simp [quickselect]
            split_ifs with h3
            · simp
            · simp at h3
              omega
          · simp at h2
        · intro h_even
          simp [implementation] at h_even ⊢
          split_ifs at h_even with h1 h2
          · contradiction
          · simp at h2
            omega
          · simp [quickselect]
            split_ifs with h3 h4
            · simp
            · simp at h3
              omega
            · simp at h4
              omega
            · simp at h3 h4
              omega