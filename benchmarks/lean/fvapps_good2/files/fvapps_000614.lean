-- <vc-preamble>
def list_max (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl Nat.max h t

def list_min (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl Nat.min h t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_tallest_mountain (n : Nat) (heights : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_tallest_in_list {n : Nat} {heights : List Nat} (h : heights ≠ []) :
  find_tallest_mountain n heights ∈ heights
  :=
sorry

theorem length_preserved {n : Nat} {heights : List Nat} :
  heights.length = n →
  heights.length = n
  :=
sorry

theorem single_mountain_height {height : Nat} :
  find_tallest_mountain 1 [height] = height
  :=
sorry
-- </vc-theorems>