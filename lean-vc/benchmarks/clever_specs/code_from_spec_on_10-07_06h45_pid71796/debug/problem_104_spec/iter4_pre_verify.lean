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
termination_by aux n _ => n

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
termination_by l.length

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
termination_by l.length

-- LLM HELPER
def List.merge (l1 l2 : List Nat) : List Nat :=
  match l1, l2 with
  | [], l => l
  | l, [] => l
  | h1 :: t1, h2 :: t2 =>
    if h1 ≤ h2 then h1 :: List.merge t1 (h2 :: t2)
    else h2 :: List.merge (h1 :: t1) t2
termination_by l1.length + l2.length

-- LLM HELPER
lemma List.mem_mergeSort (l : List Nat) (a : Nat) :
  a ∈ List.mergeSort l ↔ a ∈ l := by
  induction l using List.mergeSort.induct
  · simp [List.mergeSort]
  · simp [List.mergeSort]
  · case case3 l h =>
    simp [List.mergeSort]
    let n := l.length / 2
    let left := l.take n
    let right := l.drop n
    rw [List.mem_merge, h.1, h.2, List.mem_append, List.mem_take, List.mem_drop]
    simp [List.take_append_drop]

-- LLM HELPER
lemma List.mem_merge (l1 l2 : List Nat) (a : Nat) :
  a ∈ List.merge l1 l2 ↔ a ∈ l1 ∨ a ∈ l2 := by
  induction l1, l2 using List.merge.induct
  · simp [List.merge]
  · simp [List.merge]
  · case case3 h1 t1 h2 t2 ih1 ih2 =>
    simp [List.merge]
    split_ifs with h
    · simp [ih1]
    · simp [ih2]

-- LLM HELPER
lemma List.sorted_mergeSort (l : List Nat) :
  List.Sorted Nat.le (List.mergeSort l) := by
  induction l using List.mergeSort.induct
  · simp [List.mergeSort, List.Sorted]
  · simp [List.mergeSort, List.Sorted]
  · case case3 l h =>
    simp [List.mergeSort]
    let n := l.length / 2
    let left := l.take n
    let right := l.drop n
    exact List.sorted_merge (h.1) (h.2)

-- LLM HELPER
lemma List.sorted_merge (l1 l2 : List Nat) :
  List.Sorted Nat.le l1 → List.Sorted Nat.le l2 → List.Sorted Nat.le (List.merge l1 l2) := by
  induction l1, l2 using List.merge.induct
  · simp [List.merge]
  · simp [List.merge]
  · case case3 h1 t1 h2 t2 ih =>
    intro h_l1 h_l2
    simp [List.merge]
    split_ifs with h
    · simp [List.Sorted] at h_l1 ⊢
      cases' t1 with t1_h t1_t
      · simp [List.merge, List.Sorted]
        exact h_l2
      · simp [List.Sorted] at h_l1
        constructor
        · exact h_l1.1
        · exact ih h_l1.2 h_l2
    · simp [List.Sorted] at h_l2 ⊢
      cases' t2 with t2_h t2_t
      · simp [List.merge, List.Sorted]
        exact h_l1
      · simp [List.Sorted] at h_l2
        constructor
        · exact Nat.le_of_not_ge (fun h_ge => h h_ge)
        · exact ih h_l1 h_l2.2

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (a : Nat) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a = true := by
  induction l with
  | nil => simp [List.filter]
  | cons h t ih =>
    simp [List.filter]
    split_ifs with h_cond
    · simp [h_cond, ih]
    · simp [h_cond, ih]

-- LLM HELPER
lemma removeDuplicates_mem_iff (l : List Nat) (a : Nat) :
  a ∈ removeDuplicates l ↔ a ∈ l := by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    constructor
    · intro h_mem
      cases' h_mem with h_eq h_in_filtered
      · simp [h_eq]
      · rw [ih] at h_in_filtered
        rw [List.mem_filter] at h_in_filtered
        simp [h_in_filtered.1]
    · intro h_mem
      cases' h_mem with h_eq h_in_t
      · simp [h_eq]
      · right
        rw [ih]
        rw [List.mem_filter]
        constructor
        · exact h_in_t
        · simp

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