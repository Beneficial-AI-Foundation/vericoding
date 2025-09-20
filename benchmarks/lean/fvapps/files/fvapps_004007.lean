-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_smallest (list : List Int) : List Int :=
  sorry

def minimum (list : List Int) : Option Int :=
  sorry

def list_eq (l1 l2 : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_smallest_length (list : List Int) :
  list = [] → remove_smallest list = [] ∧
  list ≠ [] → List.length (remove_smallest list) = List.length list - 1 :=
sorry
-- </vc-theorems>