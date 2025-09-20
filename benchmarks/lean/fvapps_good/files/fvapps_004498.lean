-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GEESE : List String := ["African", "Roman Tufted", "Toulouse", "Pilgrim", "Steinbacher"]

def goose_filter (birds : List String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_subset {birds : List String} : 
  ∀ x ∈ goose_filter birds, x ∈ birds := sorry

theorem no_geese_in_output {birds : List String} :
  ∀ x ∈ goose_filter birds, x ∉ GEESE := sorry

theorem all_non_geese_preserved {birds : List String} :
  goose_filter birds = birds.filter (λ x => x ∉ GEESE) := sorry
-- </vc-theorems>