-- <vc-preamble>
def minimum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => xs.foldl min x

def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => xs.foldl max x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (l : List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: xs => x ≤ y && isSorted (y :: xs)
-- </vc-definitions>

-- <vc-theorems>
theorem estimate_population_returns_in_range 
  {surveys : List Nat} (h1 : surveys ≠ [])
  {estimate_population : List Nat → Nat}
  : estimate_population surveys ≥ minimum surveys ∧ 
    estimate_population surveys ≤ maximum surveys := by
  sorry

theorem estimate_population_returns_nat
  {surveys : List Nat}
  {estimate_population : List Nat → Nat}
  : ∃ n : Nat, estimate_population surveys = n := by
  sorry

theorem estimate_population_preserves_input 
  {surveys : List Nat}
  {estimate_population : List Nat → Nat}
  : estimate_population surveys = estimate_population surveys := by
  sorry

theorem estimate_population_handles_duplicates 
  {surveys : List Nat} (h1 : surveys ≠ [])
  {estimate_population : List Nat → Nat}
  : estimate_population (surveys ++ surveys) ≥ minimum surveys ∧ 
    estimate_population (surveys ++ surveys) ≤ maximum surveys := by
  sorry

theorem estimate_population_sort_independent
  {surveys : List Nat}
  {estimate_population : List Nat → Nat}
  {sorted_surveys : List Nat}
  (h : surveys.length = sorted_surveys.length)
  (h2 : isSorted sorted_surveys = true)
  : estimate_population surveys = estimate_population sorted_surveys := by
  sorry
-- </vc-theorems>