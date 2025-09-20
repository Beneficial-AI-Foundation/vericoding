-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_twisted37 (arr : List Int) : List Int := sorry

def twist37 (n : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_twisted37_invariants {arr : List Int} :
  let result := sort_twisted37 arr
  (List.length result = List.length arr) ∧ 
  (∀ x, x ∈ result ↔ x ∈ arr) ∧
  (∀ i j, i < j → j < result.length → 
    let i' : Fin result.length := ⟨i, by sorry⟩
    let j' : Fin result.length := ⟨j, by sorry⟩
    twist37 (result.get i') ≤ twist37 (result.get j')) :=
sorry

theorem sort_twisted37_no_changes {arr : List Int} 
  (h : ∀ x ∈ arr, ¬ (toString x).contains '3' ∧ ¬ (toString x).contains '7') :
  sort_twisted37 arr = arr :=
sorry

theorem sort_twisted37_idempotent {arr : List Int} :
  sort_twisted37 (sort_twisted37 arr) = sort_twisted37 arr :=
sorry
-- </vc-theorems>