-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.maximum (l : List Int) : Int :=
sorry

def List.minimum (l : List Int) : Int :=
sorry

def List.sort (l : List Int) : List Int :=
sorry

def find_min_height_diff (n : Nat) (k : Nat) (heights : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_height_diff_single_window {n : Nat} {heights : List Int}
  (h1 : heights.length > 0)
  (h2 : heights.length = n)
  : find_min_height_diff n 1 heights = 0 :=
sorry
-- </vc-theorems>