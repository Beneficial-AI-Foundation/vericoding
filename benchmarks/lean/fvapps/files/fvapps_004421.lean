-- <vc-preamble>
def LePair (p1 p2: String × (String ⊕ Int)) : Prop :=
  p1.1 ≤ p2.1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_hash_to_array (d: List (String × (String ⊕ Int))) : List (String × (String ⊕ Int)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_hash_output_is_sorted (d: List (String × (String ⊕ Int))) :
  let result := convert_hash_to_array d
  List.Pairwise LePair result ∧
  (∀ x ∈ result, ∃ k v, x = (k, v)) ∧
  result = d :=
sorry

theorem convert_hash_empty_dict :
  convert_hash_to_array [] = [] :=
sorry
-- </vc-theorems>