-- <vc-preamble>
def valid_preorder_string (s : String) : Bool := sorry

def depth_never_skips (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toArray {α : Type} [Inhabited α] (t : BinTree α) : Array (Option α) := sorry 

/- If a string is in valid preorder format, then its depths should never skip levels -/
-- </vc-definitions>

-- <vc-theorems>
theorem valid_implies_no_depth_skips (s : String) :
  valid_preorder_string s → depth_never_skips s := sorry

/- When converting tree to array, it's always non-empty -/

theorem tree_to_array_nonempty {α : Type} [Inhabited α] (t : BinTree α) :
  (toArray t).size > 0 := sorry

/- When converting a tree to array, the root always exists -/

theorem tree_to_array_root_exists {α : Type} [Inhabited α] (t : BinTree α) :
  Option.isSome ((toArray t)[0]'(sorry)) := sorry

/- In array form, if left child is None then right child must be None -/  

theorem array_child_property {α : Type} [Inhabited α] (t : BinTree α) 
  (i : Nat) (h1 : 1 ≤ i) (h2 : i < (toArray t).size - 1) (h3 : i % 2 = 1) :
  Option.isNone ((toArray t)[i]'(sorry)) → Option.isNone ((toArray t)[i+1]'(sorry)) := sorry

/-
info: [1, 2, 5, 3, 4, 6, 7]
-/
-- #guard_msgs in
-- #eval to_array recoverFromPreorder("1-2--3--4-5--6--7")

/-
info: [1, 2, 5, 3, None, 6, None, 4, None, 7]
-/
-- #guard_msgs in
-- #eval to_array recoverFromPreorder("1-2--3---4-5--6---7")

/-
info: [1, 401, None, 349, 88, 90]
-/
-- #guard_msgs in
-- #eval to_array recoverFromPreorder("1-401--349---90--88")
-- </vc-theorems>