-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | h::t => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def baubles_on_tree (baubles : Nat) (branches : Nat) : List Nat × String := sorry

theorem baubles_distribution (baubles : Nat) (branches : Nat)
  (h1 : baubles ≤ 1000)
  (h2 : branches ≤ 100) 
  (h3 : branches > 0) : 
  let (list, _) := baubles_on_tree baubles branches
  -- Sum equals input baubles
  List.sum list = baubles ∧ 
  -- Length equals branches 
  list.length = branches ∧
  -- Max difference ≤ 1
  (∀ x y, x ∈ list → y ∈ list → x - y ≤ 1) ∧
  -- All non-negative
  (∀ x, x ∈ list → x ≥ 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_branches (baubles : Nat) (h : baubles ≤ 1000) :
  let (_, msg) := baubles_on_tree baubles 0
  msg = "Grandma, we will have to buy a Christmas tree first!" := sorry

theorem zero_baubles (branches : Nat) (h1 : branches ≤ 100) (h2 : branches > 0) :
  let (list, _) := baubles_on_tree 0 branches
  list.length = branches ∧
  (∀ x, x ∈ list → x = 0) := sorry

/-
info: [1, 1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval baubles_on_tree 5 5

/-
info: 'Grandma, we will have to buy a Christmas tree first!'
-/
-- #guard_msgs in
-- #eval baubles_on_tree 5 0

/-
info: [2, 1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval baubles_on_tree 6 5
-- </vc-theorems>