-- <vc-preamble>
def maximum : List Nat → Nat 
  | [] => 0
  | (x::xs) => max x (maximum xs)

def minimum : List Nat → Nat
  | [] => 0
  | (x::xs) => min x (minimum xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_rect (heights : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_rect_empty :
  largest_rect [] = 0 :=
  sorry
-- </vc-theorems>