def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  ∀ x : Nat, lst.count x = result.count x ∧
  result.length = lst.length ∧
  (∀ i j : Nat, i < j → j < result.length →
    (Nat.repr (result[i]!)).length < (Nat.repr (result[j]!)).length ∨
    ((Nat.repr (result[i]!)).length = (Nat.repr (result[j]!)).length ∧ result[i]! < result[j]!))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def binaryDigitCount (n : Nat) : Nat := 
  if n = 0 then 1 else (Nat.repr n).length

-- LLM HELPER
def sortKey (n : Nat) : Nat × Nat := (binaryDigitCount n, n)

-- LLM HELPER
def insert (x : Nat) (l : List Nat) : List Nat :=
  let key := sortKey x
  let rec insertRec (l : List Nat) : List Nat :=
    match l with
    | [] => [x]
    | h :: t => 
      let hkey := sortKey h
      if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
        x :: l
      else
        h :: insertRec t
  insertRec l

-- LLM HELPER
def insertionSort (lst : List Nat) : List Nat :=
  lst.foldl (fun acc x => insert x acc) []

def implementation (lst: List Nat) : List Nat := insertionSort lst

-- LLM HELPER
lemma binaryDigitCount_eq_repr_length (n : Nat) : 
  binaryDigitCount n = (Nat.repr n).length := by
  unfold binaryDigitCount
  if h : n = 0 then
    simp [h, Nat.repr]
  else
    simp [h]

-- LLM HELPER
lemma count_insert (x y : Nat) (l : List Nat) :
  (insert x l).count y = l.count y + if x = y then 1 else 0 := by
  unfold insert
  let rec go (l : List Nat) : (insert.insertRec x l).count y = l.count y + if x = y then 1 else 0 := by
    match l with
    | [] => simp [insert.insertRec]
    | h :: t =>
      simp [insert.insertRec]
      split
      · simp [List.count_cons]
        if h_eq : x = y then
          simp [h_eq]
        else
          simp [h_eq]
      · simp [List.count_cons]
        rw [go t]
        ring
  exact go l

-- LLM HELPER
lemma length_insert (x : Nat) (l : List Nat) :
  (insert x l).length = l.length + 1 := by
  unfold insert
  let rec go (l : List Nat) : (insert.insertRec x l).length = l.length + 1 := by
    match l with
    | [] => simp [insert.insertRec]
    | h :: t =>
      simp [insert.insertRec]
      split
      · simp
      · simp [go t]
  exact go l

-- LLM HELPER
lemma count_foldl_insert (x : Nat) (lst : List Nat) :
  (lst.foldl (fun acc y => insert y acc) []).count x = lst.count x := by
  induction lst with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    rw [count_insert, ih]
    simp [List.count_cons]

-- LLM HELPER
lemma length_foldl_insert (lst : List Nat) :
  (lst.foldl (fun acc y => insert y acc) []).length = lst.length := by
  induction lst with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    rw [length_insert, ih]
    simp

-- LLM HELPER
lemma insert_preserves_sorted (x : Nat) (l : List Nat) :
  (∀ i j : Nat, i < j → j < l.length →
    (Nat.repr (l[i]!)).length < (Nat.repr (l[j]!)).length ∨
    ((Nat.repr (l[i]!)).length = (Nat.repr (l[j]!)).length ∧ l[i]! < l[j]!)) →
  (∀ i j : Nat, i < j → j < (insert x l).length →
    (Nat.repr ((insert x l)[i]!)).length < (Nat.repr ((insert x l)[j]!)).length ∨
    ((Nat.repr ((insert x l)[i]!)).length = (Nat.repr ((insert x l)[j]!)).length ∧ (insert x l)[i]! < (insert x l)[j]!)) := by
  intro h_sorted i j h_lt h_bound
  unfold insert
  let rec go (l : List Nat) : 
    (∀ i j : Nat, i < j → j < l.length →
      (Nat.repr (l[i]!)).length < (Nat.repr (l[j]!)).length ∨
      ((Nat.repr (l[i]!)).length = (Nat.repr (l[j]!)).length ∧ l[i]! < l[j]!)) →
    (∀ i j : Nat, i < j → j < (insert.insertRec x l).length →
      (Nat.repr ((insert.insertRec x l)[i]!)).length < (Nat.repr ((insert.insertRec x l)[j]!)).length ∨
      ((Nat.repr ((insert.insertRec x l)[i]!)).length = (Nat.repr ((insert.insertRec x l)[j]!)).length ∧ (insert.insertRec x l)[i]! < (insert.insertRec x l)[j]!)) := by
    match l with
    | [] => 
      intro _ _ _ h_lt h_bound
      simp [insert.insertRec] at h_lt h_bound
      omega
    | h :: t =>
      intro h_sorted_l i j h_lt h_bound
      simp [insert.insertRec] at h_bound
      split
      · simp [insert.insertRec]
        by_cases h_i : i = 0
        · simp [h_i]
          have h_j : j ≥ 1 := by omega
          cases' j with j'
          · omega
          · simp [binaryDigitCount_eq_repr_length]
            left
            unfold binaryDigitCount
            simp
            have h_cond : sortKey x ≤ sortKey h := by
              simp [sortKey]
              apply Decidable.of_decide_eq_true
              assumption
            simp [sortKey] at h_cond
            cases' h_cond with h1 h2
            · exact h1
            · exact h2.1
        · simp [h_i]
          have h_pos : i ≥ 1 := by omega
          cases' i with i'
          · omega
          · cases' j with j'
            · omega
            · simp
              apply h_sorted_l
              omega
              omega
      · simp [insert.insertRec]
        by_cases h_i : i = 0
        · simp [h_i]
          have h_j : j ≥ 1 := by omega
          cases' j with j'
          · omega
          · simp
            apply h_sorted_l
            omega
            omega
        · simp [h_i]
          have h_pos : i ≥ 1 := by omega
          cases' i with i'
          · omega
          · cases' j with j'
            · omega
            · simp
              apply go t
              · intro i j h_lt h_bound
                apply h_sorted_l
                omega
                omega
              · omega
              · omega
  exact go l h_sorted i j h_lt h_bound

-- LLM HELPER
lemma foldl_insert_sorted (lst : List Nat) :
  let result := lst.foldl (fun acc y => insert y acc) []
  ∀ i j : Nat, i < j → j < result.length →
    (Nat.repr (result[i]!)).length < (Nat.repr (result[j]!)).length ∨
    ((Nat.repr (result[i]!)).length = (Nat.repr (result[j]!)).length ∧ result[i]! < result[j]!) := by
  intro i j h_lt h_bound
  induction lst with
  | nil => 
    simp [List.foldl] at h_bound
    omega
  | cons h t ih =>
    simp [List.foldl] at h_bound ⊢
    apply insert_preserves_sorted
    exact ih

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec implementation insertionSort
  use lst.foldl (fun acc x => insert x acc) []
  constructor
  · rfl
  · intro x
    constructor
    · exact count_foldl_insert x lst
    · constructor
      · exact length_foldl_insert lst
      · exact foldl_insert_sorted lst