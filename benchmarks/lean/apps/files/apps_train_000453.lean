def abs (n : Int) : Int := 
  if n ≥ 0 then n else -n

def maxValueAfterReverse (nums : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def diffSum (nums : List Int) : Int :=
  match nums with
  | [] => 0
  | [_] => 0
  | x :: xs => List.foldl (fun acc (pair : Int × Int) => acc + abs (pair.1 - pair.2)) 0 (List.zip (x::xs) xs)

theorem maxValueAfterReverse_nonnegative (nums : List Int) :
  maxValueAfterReverse nums ≥ 0 :=
  sorry

theorem maxValueAfterReverse_geq_base (nums : List Int) :
  maxValueAfterReverse nums ≥ diffSum nums :=
  sorry

theorem maxValueAfterReverse_small_lists {nums : List Int} (h : nums.length ≤ 2) :
  match nums with
  | [] => maxValueAfterReverse nums = 0
  | [_] => maxValueAfterReverse nums = 0 
  | [x, y] => maxValueAfterReverse nums = abs (x - y)
  | _ => True
  :=
  sorry

theorem maxValueAfterReverse_monotonic_defined (nums : List Int) (h : nums.length ≥ 3) :
  ∃ (n n' : Int), maxValueAfterReverse nums = n :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval maxValueAfterReverse [2, 3, 1, 5, 4]

/-
info: 68
-/
-- #guard_msgs in
-- #eval maxValueAfterReverse [2, 4, 9, 24, 2, 1, 10]

/-
info: 8
-/
-- #guard_msgs in
-- #eval maxValueAfterReverse [1, 2, 3, 4, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded