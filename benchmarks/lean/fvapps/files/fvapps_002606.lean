-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cube_odd (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cube_odd_integers (xs : List Int) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_bounded (xs : List Int) 
  (h : ∀ x ∈ xs, -1000 ≤ x ∧ x ≤ 1000) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_non_empty (xs : List Int)
  (h : xs ≠ []) : 
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry
-- </vc-theorems>