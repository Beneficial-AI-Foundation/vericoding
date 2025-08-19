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
  if n = 0 then 1 else Nat.log 2 n + 1

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
    sorry

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
lemma foldl_insert_sorted (lst : List Nat) :
  let result := lst.foldl (fun acc y => insert y acc) []
  ∀ i j : Nat, i < j → j < result.length →
    (Nat.repr (result[i]!)).length < (Nat.repr (result[j]!)).length ∨
    ((Nat.repr (result[i]!)).length = (Nat.repr (result[j]!)).length ∧ result[i]! < result[j]!) := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
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