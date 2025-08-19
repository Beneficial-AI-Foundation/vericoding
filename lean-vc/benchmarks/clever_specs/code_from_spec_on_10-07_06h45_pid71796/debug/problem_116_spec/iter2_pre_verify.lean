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
    Nat.digits 2 (result.get! i) < Nat.digits 2 (result.get! j) ∨
    (Nat.digits 2 (result.get! i) = Nat.digits 2 (result.get! j) ∧ result.get! i < result.get! j))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def binaryDigitCount (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def sortKey (n : Nat) : Nat × Nat := (binaryDigitCount n, n)

-- LLM HELPER
def insertionSort (lst : List Nat) : List Nat :=
  lst.foldl (fun acc x => 
    let key := sortKey x
    let rec insert (l : List Nat) : List Nat :=
      match l with
      | [] => [x]
      | h :: t => 
        let hkey := sortKey h
        if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
          x :: l
        else
          h :: insert t
    insert acc
  ) []

def implementation (lst: List Nat) : List Nat := insertionSort lst

-- LLM HELPER
lemma count_foldl_insert (x : Nat) (lst : List Nat) :
  (lst.foldl (fun acc y => 
    let key := sortKey y
    let rec insert (l : List Nat) : List Nat :=
      match l with
      | [] => [y]
      | h :: t => 
        let hkey := sortKey h
        if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
          y :: l
        else
          h :: insert t
    insert acc
  ) []).count x = lst.count x := by
  induction lst with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    sorry

-- LLM HELPER
lemma length_foldl_insert (lst : List Nat) :
  (lst.foldl (fun acc y => 
    let key := sortKey y
    let rec insert (l : List Nat) : List Nat :=
      match l with
      | [] => [y]
      | h :: t => 
        let hkey := sortKey h
        if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
          y :: l
        else
          h :: insert t
    insert acc
  ) []).length = lst.length := by
  induction lst with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    sorry

-- LLM HELPER
lemma foldl_insert_sorted (lst : List Nat) :
  let result := lst.foldl (fun acc y => 
    let key := sortKey y
    let rec insert (l : List Nat) : List Nat :=
      match l with
      | [] => [y]
      | h :: t => 
        let hkey := sortKey h
        if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
          y :: l
        else
          h :: insert t
    insert acc
  ) []
  ∀ i j : Nat, i < j → j < result.length →
    Nat.digits 2 (result.get! i) < Nat.digits 2 (result.get! j) ∨
    (Nat.digits 2 (result.get! i) = Nat.digits 2 (result.get! j) ∧ result.get! i < result.get! j) := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation insertionSort
  use lst.foldl (fun acc x => 
    let key := sortKey x
    let rec insert (l : List Nat) : List Nat :=
      match l with
      | [] => [x]
      | h :: t => 
        let hkey := sortKey h
        if key.1 < hkey.1 || (key.1 = hkey.1 && key.2 <= hkey.2) then
          x :: l
        else
          h :: insert t
    insert acc
  ) []
  constructor
  · rfl
  · intro x
    constructor
    · exact count_foldl_insert x lst
    · constructor
      · exact length_foldl_insert lst
      · exact foldl_insert_sorted lst