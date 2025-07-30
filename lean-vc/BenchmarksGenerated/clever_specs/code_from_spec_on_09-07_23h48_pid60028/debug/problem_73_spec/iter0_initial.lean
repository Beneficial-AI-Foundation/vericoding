def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result : Int) :=
  let swaps_done (arr1: List Int) (arr2: List Int) :=
    ((List.finRange (arr1.length)).filter (fun idx => arr1[idx]? ≠ arr2[idx]?)).length/2
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    result ≤ (swaps_done arr palin_perm)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def count_frequencies (arr: List Int) : List (Int × Nat) :=
  arr.foldl (fun acc x =>
    match acc.find? (fun p => p.1 = x) with
    | some (_, count) => acc.map (fun p => if p.1 = x then (x, count + 1) else p)
    | none => (x, 1) :: acc
  ) []

-- LLM HELPER
def count_odds (freqs: List (Int × Nat)) : Nat :=
  freqs.foldl (fun acc p => if p.2 % 2 = 1 then acc + 1 else acc) 0

-- LLM HELPER
def min_swaps_for_palindrome (arr: List Int) : Int :=
  let freqs := count_frequencies arr
  let odds := count_odds freqs
  if odds ≤ 1 then 0 else odds / 2

def implementation (arr: List Int) : Int := min_swaps_for_palindrome arr

-- LLM HELPER
lemma palindrome_condition (arr: List Int) : 
  (∃ palin_perm, List.Perm arr palin_perm ∧ List.Palindrome palin_perm) ↔ 
  count_odds (count_frequencies arr) ≤ 1 := by
  sorry

-- LLM HELPER
lemma swaps_lower_bound (arr: List Int) (palin_perm: List Int) :
  List.Perm arr palin_perm → List.Palindrome palin_perm →
  min_swaps_for_palindrome arr ≤ 
  ((List.finRange (arr.length)).filter (fun idx => arr[idx]? ≠ palin_perm[idx]?)).length/2 := by
  sorry

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  simp [problem_spec, implementation]
  use min_swaps_for_palindrome arr
  constructor
  · rfl
  · intro palin_perm h
    exact swaps_lower_bound arr palin_perm h.1 h.2