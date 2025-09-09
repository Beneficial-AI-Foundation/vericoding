-- <vc-helpers>
-- </vc-helpers>

def db_sort : List α → List α := sorry

def isSorted [LE α] [Inhabited α] (l : List α) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

theorem db_sort_numbers_sorted [LE Int] [Inhabited Int] (arr : List Int) : 
  isSorted (db_sort arr) := sorry

theorem db_sort_strings_sorted [LE String] [Inhabited String] (arr : List String) :
  isSorted (db_sort arr) := sorry

theorem db_sort_mixed_preserves_length {α} (arr : List α) :
  List.length (db_sort arr) = List.length arr := sorry

theorem db_sort_numbers_before_strings (arr : List (Int ⊕ String)) :
  let result := db_sort arr
  let nums := result.filter (fun x => match x with | Sum.inl _ => true | _ => false)
  let strs := result.filter (fun x => match x with | Sum.inr _ => true | _ => false)
  ∀ i j, i < j → i < nums.length → j ≥ nums.length →
    (match result[i]? with | some (Sum.inl _) => true | _ => false) ∧
    (match result[j]? with | some (Sum.inr _) => true | _ => false) := sorry

theorem db_sort_mixed_numbers_sorted [LE Int] [Inhabited Int] (arr : List (Int ⊕ String)) :
  let result := db_sort arr
  let nums := result.filter (fun x => match x with | Sum.inl n => true | _ => false)
  let nums_only := nums.map (fun x => match x with | Sum.inl n => n | _ => 0)
  isSorted nums_only := sorry

theorem db_sort_mixed_strings_sorted [LE String] [Inhabited String] (arr : List (Int ⊕ String)) :
  let result := db_sort arr
  let strs := result.filter (fun x => match x with | Sum.inr s => true | _ => false)
  let strs_only := strs.map (fun x => match x with | Sum.inr s => s | _ => "")
  isSorted strs_only := sorry

theorem db_sort_preserves_elements (arr : List (Int ⊕ String)) :
  List.length (db_sort arr) = List.length arr := sorry

/-
info: [2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval db_sort [6, 2, 3, 4, 5]

/-
info: [0, 2, 2, 'Apple', 'Banana', 'Mango', 'Orange']
-/
-- #guard_msgs in
-- #eval db_sort ["Banana", "Orange", "Apple", "Mango", 0, 2, 2]

/-
info: [1, 1, 1, 1, 1, 1, 2, 2, 3, '1', '2', 'three']
-/
-- #guard_msgs in
-- #eval db_sort [1, 1, 1, 1, 1, 2, "1", "2", "three", 1, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: unguarded