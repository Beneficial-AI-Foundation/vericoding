-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort : List Nat → List Nat := sorry

def solve_circle_rectangles (n : Nat) (A B : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_less_than_inputs {n : Nat} {A B : List Nat} 
  (h1 : A.length = n) (h2 : B.length = n) :
  solve_circle_rectangles n A B ≤ List.sum A ∧ 
  solve_circle_rectangles n A B ≤ List.sum B := sorry

theorem result_non_negative {n : Nat} {A B : List Nat}
  (h1 : A.length = n) (h2 : B.length = n) :
  solve_circle_rectangles n A B ≥ 0 := sorry

theorem result_order_independent {n : Nat} {A B : List Nat}
  (h1 : A.length = n) (h2 : B.length = n) :
  solve_circle_rectangles n A B = 
  solve_circle_rectangles n A.reverse B.reverse := sorry

theorem result_is_sum_of_mins {n : Nat} {A B : List Nat}
  (h1 : A.length = n) (h2 : B.length = n) :
  solve_circle_rectangles n A B = 
  List.sum (List.map (fun (p : Nat × Nat) => min p.fst p.snd) 
    (List.zip (List.sort A) (List.sort B))) := sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval solve_circle_rectangles 4 [8, 8, 10, 12] [15, 20, 3, 5]

/-
info: 30
-/
-- #guard_msgs in
-- #eval solve_circle_rectangles 3 [20, 20, 20] [10, 10, 10]
-- </vc-theorems>