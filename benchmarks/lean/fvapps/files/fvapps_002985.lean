-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def index (arr : List Int) (n : Nat) : Int := sorry

theorem index_valid_index {arr : List Int} {n : Nat} (h : n < arr.length) :
  index arr n = (arr.get ⟨n, h⟩) ^ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem index_invalid_index {arr : List Int} {n : Nat} (h : n ≥ arr.length) :
  index arr n = -1 := sorry

theorem index_empty_array {n : Nat} :
  index [] n = -1 := sorry
-- </vc-theorems>