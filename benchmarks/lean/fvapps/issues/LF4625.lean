-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def makeParts {α : Type u} (lst : List α) (chunkSize : Nat) : List (List α) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem makeParts_chunk_size_property {α : Type u} (lst : List α) (chunkSize : Nat) 
  (h : chunkSize > 0) :
  ∀ i, i < (makeParts lst chunkSize).length - 1 → 
  ((makeParts lst chunkSize)[i]'(by sorry)).length = chunkSize := 
  sorry

theorem makeParts_last_chunk_size {α : Type u} (lst : List α) (chunkSize : Nat)
  (h1 : chunkSize > 0) (h2 : (makeParts lst chunkSize).length > 0) :
  let parts := makeParts lst chunkSize
  (parts[parts.length - 1]'(by sorry)).length ≤ chunkSize :=
  sorry

theorem makeParts_preserves_elements {α : Type u} (lst : List α) (chunkSize : Nat)
  (h : chunkSize > 0) :
  (makeParts lst chunkSize).join = lst :=
  sorry

theorem makeParts_chunk_count {α : Type u} (lst : List α) (chunkSize : Nat)
  (h : chunkSize > 0) :
  (makeParts lst chunkSize).length = (lst.length + chunkSize - 1) / chunkSize :=
  sorry

theorem makeParts_chunk_size_one {α : Type u} (lst : List α) :
  makeParts lst 1 = lst.map (·::List.nil) :=
  sorry

theorem makeParts_full_list {α : Type u} (lst : List α) (h : lst.length > 0) :
  makeParts lst lst.length = [lst] :=
  sorry

theorem makeParts_empty_list {α : Type u} (n : Nat) (h : n > 0) :
  makeParts ([] : List α) n = [] :=
  sorry

/-
info: [[1, 2], [3, 4], [5, 6]]
-/
-- #guard_msgs in
-- #eval make_parts [1, 2, 3, 4, 5, 6] 2

/-
info: [[1, 2], [3, 4], [5]]
-/
-- #guard_msgs in
-- #eval make_parts [1, 2, 3, 4, 5] 2

/-
info: []
-/
-- #guard_msgs in
-- #eval make_parts [] 3
-- </vc-theorems>