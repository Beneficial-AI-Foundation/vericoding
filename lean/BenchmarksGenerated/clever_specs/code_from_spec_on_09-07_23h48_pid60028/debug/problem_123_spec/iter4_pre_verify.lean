def problem_spec
-- function signature
(impl: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
n > 0 →
List.Sorted (· < ·) result ∧
∀ m, m ∈ result ↔ Odd m ∧ collatz_reachable n m -- m is reachable from starting point n
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def Odd (n : Nat) : Prop := n % 2 = 1

-- LLM HELPER
def collatz_reachable (n m : Nat) : Prop :=
  ∃ k, collatz_iter n k = m

-- LLM HELPER
def collatz_iter (n : Nat) : Nat → Nat
  | 0 => n
  | k+1 => collatz_step (collatz_iter n k)

-- LLM HELPER  
def collatz_step (n : Nat) : Nat :=
  if n = 1 then 1
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

-- LLM HELPER
def collect_odd_reachable (n : Nat) (max_steps : Nat) : List Nat :=
  let visited := collect_path n max_steps
  (visited.toList.filter Odd).mergeSort (· ≤ ·)

-- LLM HELPER
def collect_path (n : Nat) (max_steps : Nat) : Finset Nat :=
  let rec aux (current : Nat) (steps : Nat) (acc : Finset Nat) : Finset Nat :=
    if steps = 0 ∨ current = 1 then acc.insert current
    else 
      let next := collatz_step current
      aux next (steps - 1) (acc.insert current)
  aux n max_steps ∅

-- LLM HELPER
def max_bound (n : Nat) : Nat := 1000 * n

def implementation (n: Nat) : List Nat := 
  if n = 0 then []
  else collect_odd_reachable n (max_bound n)

-- LLM HELPER
theorem collatz_reachable_refl (n : Nat) : collatz_reachable n n := by
  use 0
  rfl

-- LLM HELPER
theorem odd_filter_sorted (l : List Nat) : List.Sorted (· < ·) (l.filter Odd).mergeSort (· ≤ ·) := by
  exact List.sorted_mergeSort _

-- LLM HELPER
theorem collect_path_contains_start (n : Nat) (k : Nat) : n ∈ collect_path n k := by
  simp [collect_path]
  sorry

-- LLM HELPER
theorem implementation_contains_reachable_odds (n : Nat) (h : n > 0) : 
  ∀ m, m ∈ implementation n → Odd m ∧ collatz_reachable n m := by
  intro m hm
  simp [implementation] at hm
  simp [h] at hm
  simp [collect_odd_reachable] at hm
  sorry

-- LLM HELPER
theorem implementation_complete_for_reachable_odds (n : Nat) (h : n > 0) :
  ∀ m, Odd m ∧ collatz_reachable n m → m ∈ implementation n := by
  intro m ⟨hodd, hreach⟩
  simp [implementation, h, collect_odd_reachable]
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    constructor
    · -- Sorted
      simp [implementation, h]
      exact odd_filter_sorted _
    · -- Membership characterization
      intro m
      constructor
      · -- If m ∈ result, then Odd m ∧ collatz_reachable n m
        exact implementation_contains_reachable_odds n h m
      · -- If Odd m ∧ collatz_reachable n m, then m ∈ result
        exact implementation_complete_for_reachable_odds n h m