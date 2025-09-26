-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toString : Nat → String := sorry
def unused_digits : List Nat → String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unused_digits_length (args: List Nat) (result: String) :
  result = unused_digits args →
  (match args with
  | [0] => result.length = 9
  | [9] => result.length = 9
  | [12, 34] => result.length = 6
  | [123, 456, 789] => result.length = 1
  | [1111] => result.length = 9
  | [42] => result.length = 8
  | _ => True) := sorry

theorem unused_digits_all_chars_are_digits (args: List Nat) :
  ∀ c, c ∈ (unused_digits args).data → 
    '0' ≤ c ∧ c ≤ '9' := sorry

theorem unused_digits_is_ordered (args: List Nat) :
  let s := unused_digits args
  ∀ (i j : Fin s.length), i.val < j.val →
    s.data[i.val]! ≤ s.data[j.val]! := sorry

theorem unused_digits_complement_size (args: List Nat) :
  let used := List.join (args.map (fun n => (toString n).data))
  (unused_digits args).length + used.length = 10 := sorry

theorem unused_digits_no_intersection (args: List Nat) :
  let used := List.join (args.map (fun n => (toString n).data))
  let unused := (unused_digits args).data
  ∀ c, c ∈ unused → c ∉ used := sorry

theorem unused_digits_all_unique (args: List Nat) :
  let chars := (unused_digits args).data
  List.Nodup chars := sorry

theorem unused_digits_specific_values :
  unused_digits [12, 34, 56, 78] = "09" ∧
  unused_digits [2015, 8, 26] = "3479" ∧
  unused_digits [93, 10, 11, 40] = "25678" := sorry

/-
info: '09'
-/
-- #guard_msgs in
-- #eval unused_digits 12 34 56 78

/-
info: '3479'
-/
-- #guard_msgs in
-- #eval unused_digits 2015 8 26

/-
info: '25678'
-/
-- #guard_msgs in
-- #eval unused_digits 93 10 11 40
-- </vc-theorems>