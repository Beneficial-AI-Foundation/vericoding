-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_nice (arr : List Int) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nice_list_nonempty {arr : List Int} : 
  is_nice arr → arr ≠ [] :=
  sorry

theorem nice_list_has_neighbors {arr : List Int} {n : Int} :
  is_nice arr → n ∈ arr → 
  (n + 1 ∈ arr) ∨ (n - 1 ∈ arr) :=
  sorry

theorem empty_list_not_nice :
  ¬is_nice [] :=
  sorry

theorem singleton_not_nice (x : Int) :
  ¬is_nice [x] :=
  sorry

theorem sequential_is_nice_ascending :
  is_nice [0, 1, 2] :=
  sorry

theorem sequential_is_nice_negative :
  is_nice [-2, -1, 0] :=
  sorry

theorem sequential_is_nice_descending :
  is_nice [10, 9, 8] :=
  sorry
-- </vc-theorems>