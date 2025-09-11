-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum (l : List Int) : Int := sorry

def slidemax (nums : List Int) (k : Nat) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slidemax_matches_window_max
  (nums : List Int) (k : Nat)
  (h1 : 0 < k) 
  (h2 : k ≤ nums.length) :
  slidemax nums k = 
    (List.range (nums.length + 1 - k)).map (fun i =>
      maximum (List.take k (List.drop i nums))) := sorry

theorem slidemax_length
  (nums : List Int) (k : Nat)
  (h1 : 0 < k)
  (h2 : k ≤ nums.length) :
  (slidemax nums k).length = nums.length + 1 - k := sorry

/-
info: [10, 15, 16]
-/
-- #guard_msgs in
-- #eval solve 3 3 [[3, 2, 4, 8], [2, 2, 5], [2, 6, 3]]

/-
info: [7, 8]
-/
-- #guard_msgs in
-- #eval solve 2 2 [[2, 7, 8], [1, -8]]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded