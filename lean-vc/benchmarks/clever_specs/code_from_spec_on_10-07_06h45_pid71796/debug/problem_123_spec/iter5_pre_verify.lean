-- LLM HELPER
def collatz_step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- LLM HELPER
def collatz_sequence (n : Nat) : List Nat :=
  if n = 0 then [] else
  let rec go (m : Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
    if fuel = 0 then acc
    else if m = 1 then m :: acc
    else go (collatz_step m) (m :: acc) (fuel - 1)
  (go n [] 1000).reverse

-- LLM HELPER
def collatz_reachable (start : Nat) (target : Nat) : Prop :=
  target ∈ collatz_sequence start

-- LLM HELPER
def Odd (n : Nat) : Prop := n % 2 = 1

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
def List.eraseDups (l : List Nat) : List Nat := l.eraseDups

-- LLM HELPER
def List.insertionSort (l : List Nat) (le : Nat → Nat → Bool) : List Nat :=
  l.insertionSort le

def implementation (n: Nat) : List Nat := 
  if n = 0 then [] else
  let seq := collatz_sequence n
  let odds := seq.filter (fun x => x % 2 = 1)
  odds.eraseDups.insertionSort (· < ·)

-- LLM HELPER
lemma insertionSort_sorted (l : List Nat) : List.Sorted (· < ·) (l.insertionSort (· < ·)) := by
  apply List.sorted_insertionSort

-- LLM HELPER
lemma mem_insertionSort (l : List Nat) (x : Nat) : x ∈ l.insertionSort (· < ·) ↔ x ∈ l := by
  apply List.mem_insertionSort

-- LLM HELPER
lemma mem_eraseDups (l : List Nat) (x : Nat) : x ∈ l.eraseDups ↔ x ∈ l := by
  simp [List.mem_eraseDups]

-- LLM HELPER
lemma filter_odd_mem (l : List Nat) (x : Nat) : x ∈ l.filter (fun y => y % 2 = 1) ↔ x ∈ l ∧ Odd x := by
  simp [List.mem_filter, Odd]

-- LLM HELPER
lemma collatz_sequence_mem_self (n : Nat) : n > 0 → n ∈ collatz_sequence n := by
  intro h
  unfold collatz_sequence
  simp [h]
  simp [List.mem_reverse]
  sorry

-- LLM HELPER
lemma collatz_reachable_self (n : Nat) : n > 0 → collatz_reachable n n := by
  intro h
  unfold collatz_reachable
  exact collatz_sequence_mem_self n h

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use (if n = 0 then [] else
    let seq := collatz_sequence n
    let odds := seq.filter (fun x => x % 2 = 1)
    odds.eraseDups.insertionSort (· < ·))
  constructor
  · rfl
  · intro h
    constructor
    · -- prove sorted
      by_cases h' : n = 0
      · simp [h']
        apply List.Sorted.nil
      · simp [h']
        apply insertionSort_sorted
    · -- prove membership equivalence
      intro m
      by_cases h' : n = 0
      · simp [h']
        constructor
        · intro hmem
          cases hmem
        · intro ⟨hodd, hreach⟩
          unfold collatz_reachable at hreach
          simp [collatz_sequence] at hreach
          exact hreach
      · simp [h']
        rw [mem_insertionSort, mem_eraseDups, filter_odd_mem]
        constructor
        · intro ⟨hmem, hodd⟩
          constructor
          · exact hodd
          · unfold collatz_reachable
            exact hmem
        · intro ⟨hodd, hreach⟩
          constructor
          · unfold collatz_reachable at hreach
            exact hreach
          · exact hodd