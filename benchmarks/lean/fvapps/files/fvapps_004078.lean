-- <vc-preamble>
def sumList : List Int → Int 
  | [] => 0
  | (x::xs) => x + sumList xs

def lengthList : List Int → Int
  | [] => 0
  | (_::xs) => 1 + lengthList xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def better_than_average (class_points: List Int) (your_points: Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem better_than_average_spec {class_points: List Int} {your_points: Int}
  (h: class_points ≠ []) :
  better_than_average class_points your_points = 
    (your_points > (sumList class_points / lengthList class_points)) :=
  sorry

theorem better_than_average_edge_cases1 :
  better_than_average [0] 0 = false :=
  sorry

theorem better_than_average_edge_cases2 :
  better_than_average [1] 1 = false :=
  sorry

theorem better_than_average_edge_cases3 :
  better_than_average [0] 1 = true :=
  sorry
-- </vc-theorems>