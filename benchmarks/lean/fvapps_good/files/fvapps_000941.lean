-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pos_search (arr : List Int) (num : Int) : Nat := sorry 
def solve_walls (n : Nat) (walls : List Int) (queries : List (Int × Int)) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pos_search_empty_array {num : Int} : 
  pos_search [] num = 0 := sorry

theorem pos_search_num_present {arr : List Int} {num : Int} (h : arr.contains num) :
  pos_search arr num = 0 := sorry

theorem pos_search_bounds {arr : List Int} {num : Int} (h : ¬arr.contains num) :
  pos_search arr num ≤ arr.length := sorry

theorem pos_search_left_elements {arr : List Int} {num : Int} (h₁ : ¬arr.contains num) 
  (h₂ : pos_search arr num > 0) :
  ∀ x ∈ arr.take (pos_search arr num), x < num := sorry

theorem pos_search_right_elements {arr : List Int} {num : Int} (h₁ : ¬arr.contains num)
  (h₂ : pos_search arr num < arr.length) :
  ∀ x ∈ arr.drop (pos_search arr num), num < x := sorry

theorem solve_walls_length {n : Nat} {walls : List Int} {queries : List (Int × Int)} :
  (solve_walls n walls queries).length = queries.length := sorry

theorem solve_walls_matches_pos_search {n : Nat} {walls : List Int} {queries : List (Int × Int)}
  {i : Fin queries.length} :
  (solve_walls n walls queries).get ⟨i.val, by simp [solve_walls_length]⟩ = 
    pos_search walls ((queries.get i).1 + (queries.get i).2) := sorry
-- </vc-theorems>