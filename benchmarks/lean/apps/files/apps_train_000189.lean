-- <vc-preamble>
def sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + sum t

def min_set_size (arr : List Int) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listRange (n : Nat) : List Int :=
  (List.range n).map Int.ofNat
-- </vc-definitions>

-- <vc-theorems>
theorem min_set_size_positive (arr : List Int) (h : arr ≠ []) :
  min_set_size arr > 0 :=
  sorry

theorem min_set_size_upper_bound (arr : List Int) (h : arr ≠ []) :
  min_set_size arr ≤ arr.length :=
  sorry

theorem min_set_size_removes_half (arr : List Int) (h : arr ≠ []) :
  let countMap := arr.map (fun x => (arr.filter (· = x)).length)
  let removed := countMap.take (min_set_size arr)
  sum removed ≥ arr.length / 2 :=
  sorry

theorem min_set_size_all_same (arr : List Int) (h : arr ≠ []) :
  (∀ i j, i < arr.length → j < arr.length → arr[i]! = arr[j]!) →
  min_set_size arr = 1 :=
  sorry

theorem min_set_size_all_unique (n : Nat) :
  min_set_size (listRange n) = (n + 1) / 2 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_set_size [3, 3, 3, 3, 5, 5, 5, 2, 2, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_set_size [7, 7, 7, 7, 7, 7]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_set_size [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded