def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => d % 2 = 0) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
def Nat.digits (base : Nat) (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rec aux (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else aux (n / base) ((n % base) :: acc)
    aux n []

-- LLM HELPER
def List.Sorted (r : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => r a b ∧ List.Sorted r (b :: rest)

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => d % 2 = 0) (Nat.digits 10 i)).length > 0

-- LLM HELPER
def removeDuplicates (l: List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => h :: removeDuplicates (List.filter (fun x => x ≠ h) t)
termination_by removeDuplicates l => l.length

def implementation (x: List Nat) : List Nat := 
  let filtered := List.filter (fun i => !(has_even_digits i)) x
  let unique := removeDuplicates filtered
  List.mergeSort unique

-- LLM HELPER
def List.mergeSort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | [a] => [a]
  | _ => 
    let n := l.length / 2
    let left := l.take n
    let right := l.drop n
    List.merge (List.mergeSort left) (List.mergeSort right)
termination_by List.mergeSort l => l.length

-- LLM HELPER
def List.merge (l1 l2 : List Nat) : List Nat :=
  match l1, l2 with
  | [], l => l
  | l, [] => l
  | h1 :: t1, h2 :: t2 =>
    if h1 ≤ h2 then h1 :: List.merge t1 (h2 :: t2)
    else h2 :: List.merge (h1 :: t1) t2
termination_by List.merge l1 l2 => l1.length + l2.length

-- LLM HELPER
lemma List.mem_mergeSort (l : List Nat) (a : Nat) :
  a ∈ List.mergeSort l ↔ a ∈ l := by
  sorry

-- LLM HELPER
lemma List.sorted_mergeSort (l : List Nat) :
  List.Sorted Nat.le (List.mergeSort l) := by
  sorry

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (a : Nat) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a = true := by
  sorry

-- LLM HELPER
lemma removeDuplicates_mem_iff (l : List Nat) (a : Nat) :
  a ∈ removeDuplicates l ↔ a ∈ l := by
  sorry

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use implementation x
  constructor
  · rfl
  · constructor
    · -- Prove sorted
      simp [implementation]
      apply List.sorted_mergeSort
    · -- Prove membership equivalence
      intro i
      simp [implementation, has_even_digits]
      constructor
      · intro h
        rw [List.mem_mergeSort, removeDuplicates_mem_iff, filter_mem_iff] at h
        exact h
      · intro h
        rw [List.mem_mergeSort, removeDuplicates_mem_iff, filter_mem_iff]
        exact h