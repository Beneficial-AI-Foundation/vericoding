-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_subset {α} [BEq α] (subset : List α) (fullset : List α) : Bool := sorry

theorem proper_subset_property {α} [BEq α] (subset additional : List α) 
  (h1 : List.Nodup subset) (h2 : List.Nodup additional) :
  check_subset subset (subset ++ additional) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem subset_reflexive {α} [BEq α] (set_a set_b : List α) 
  (h1 : List.Nodup set_a) (h2 : List.Nodup set_b) :
  check_subset set_a set_b = 
    (∀ x, x ∈ set_a → x ∈ set_b) := sorry

theorem empty_set_is_subset {α} [BEq α] (set_b : List α) 
  (h : List.Nodup set_b) :
  check_subset [] set_b = true := sorry

theorem set_is_subset_of_itself {α} [BEq α] (set_a : List α)
  (h : List.Nodup set_a) :
  check_subset set_a set_a = true := sorry

theorem disjoint_sets_not_subset {α} [BEq α] (set_a set_b : List α)
  (h1 : List.Nodup set_a) (h2 : List.Nodup set_b)
  (h3 : ¬List.isEmpty set_a)
  (h4 : ∀ x, x ∈ set_a → x ∉ set_b) :
  check_subset set_a set_b = false := sorry
-- </vc-theorems>