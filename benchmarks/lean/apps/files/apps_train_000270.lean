-- <vc-preamble>
def num_times_all_blue (lights : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_duplicates (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (lights : List Nat) (h : lights ≠ []) :
  let valid := lights.filter (fun x => x ≤ lights.length)
  let nodupes := remove_duplicates valid  
  0 ≤ num_times_all_blue nodupes ∧ num_times_all_blue nodupes ≤ nodupes.length :=
sorry

theorem permutation_correctness {n : Nat} (lights : List Nat) 
  (h1 : lights.length = n)
  (h2 : ∀ x, x ∈ lights → x ≤ n) 
  (h3 : ∀ x, x ∈ lights → (lights.filter (· = x)).length = 1) :
  num_times_all_blue lights = 
    (List.range lights.length).foldl 
      (fun acc i => 
        let rightmost := (lights.take (i+1)).foldl Nat.max 0 
        if i+1 = rightmost then acc + 1 else acc) 
      0 :=
sorry

theorem invariants (lights : List Nat) (h : lights ≠ []) :
  let valid := lights.filter (fun x => x ≤ lights.length)
  let nodupes := remove_duplicates valid
  let h2 := sorry -- proof that nodupes ≠ []
  (nodupes.getLast h2 = nodupes.length → num_times_all_blue nodupes ≥ 1) ∧ 
  num_times_all_blue nodupes ≤ nodupes.length :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_times_all_blue [2, 1, 3, 5, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_times_all_blue [3, 2, 4, 1, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_times_all_blue [4, 1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded