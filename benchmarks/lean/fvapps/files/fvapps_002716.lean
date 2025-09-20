-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split (s: String) (sep: String) : List String := sorry

def sort_reindeer (names: List String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_reindeer_length_preservation (names: List String) :
  (sort_reindeer names).length = names.length := sorry

theorem sort_reindeer_elements_preserved (names: List String) :
  ∀ x, x ∈ names ↔ x ∈ sort_reindeer names := sorry

theorem sort_reindeer_sorted_by_last_name (names: List String) :
  let result := sort_reindeer names
  ∀ i, i < result.length - 1 →
    let curr_last := (split (result[i]!) " ")[1]!
    let next_last := (split (result[i+1]!) " ")[1]!
    curr_last ≤ next_last := sorry

theorem sort_reindeer_idempotent (names: List String) :
  sort_reindeer (sort_reindeer names) = sort_reindeer names := sorry

theorem sort_reindeer_empty : 
  sort_reindeer [] = [] := sorry
-- </vc-theorems>