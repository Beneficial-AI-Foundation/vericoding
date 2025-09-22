-- <vc-preamble>
def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_minimum (lst : List Int) : Int :=
sorry

def array_center (lst : List Int) : List Int :=
sorry

def mean (lst : List Int) : Int :=
sorry

def list_index_of (lst : List Int) (x : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_center_is_subset {lst : List Int} (h : lst ≠ []) :
  ∀ x, x ∈ array_center lst → x ∈ lst :=
sorry
-- </vc-theorems>