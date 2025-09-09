def array_pair_sum (nums : List Int) : Int := sorry

def List.sorted (xs : List Int) : List Int := xs -- placeholder for sorting

def evenIndexSum (xs : List Int) : Int :=
  let rec loop : List Int → Int → Int → Int
    | [], _, acc => acc 
    | (x::xs), i, acc => loop xs (i+1) (if i % 2 = 0 then acc + x else acc)
  loop xs 0 0

-- <vc-helpers>
-- </vc-helpers>

def halfListSum (xs : List Int) : Int :=
  let rec loop : List Int → Nat → Int → Int
    | [], _, acc => acc
    | _, 0, acc => acc
    | (x::xs), n+1, acc => loop xs n (acc + x)
  loop xs (xs.length / 2) 0

theorem array_pair_sum_equals_even_indexed_sum {nums : List Int} 
  (h : nums.length % 2 = 0) :
  array_pair_sum nums = evenIndexSum (nums.sorted) := sorry

theorem array_pair_sum_geq_smallest_half_sum {nums : List Int}
  (h : nums.length % 2 = 0) :
  array_pair_sum nums ≥ halfListSum (nums.sorted) := sorry

theorem array_pair_sum_positive {nums : List Int}
  (h1 : nums.length % 2 = 0)
  (h2 : ∀ x ∈ nums, x > 0) :
  array_pair_sum nums > 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval array_pair_sum [1, 4, 3, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval array_pair_sum [1, 2, 3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval array_pair_sum [1, 1, 2, 2]

-- Apps difficulty: introductory
-- Assurance level: guarded