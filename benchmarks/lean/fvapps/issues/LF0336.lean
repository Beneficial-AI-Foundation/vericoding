-- <vc-preamble>
def splitArray (nums : List Nat) (m : Nat) : Nat := sorry

def listSum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listMax : List Nat → Nat 
  | [] => 0
  | [x] => x
  | (x::xs) => max x (listMax xs)
-- </vc-definitions>

-- <vc-theorems>
theorem splitArray_bounds (nums : List Nat) (m : Nat) (h1 : nums ≠ []) (h2 : m > 0) :
  let m' := min m (List.length nums)
  let result := splitArray nums m'
  result ≥ (listMax nums) ∧ result ≤ (listSum nums) := sorry

theorem splitArray_m_one (nums : List Nat) (h1 : nums ≠ []) :
  splitArray nums 1 = listSum nums := sorry

theorem splitArray_m_len (nums : List Nat) (h1 : nums ≠ []) :
  splitArray nums (List.length nums) = listMax nums := sorry

theorem splitArray_valid_split (nums : List Nat) (m : Nat) (h1 : nums ≠ []) (h2 : m > 0) :
  let m' := min m (List.length nums)
  let maxSum := splitArray nums m'
  ∃ splits : Nat, splits ≤ m' ∧
    ∃ partitions : List (List Nat),
      List.length partitions = splits ∧
      List.join partitions = nums ∧
      (∀ p ∈ partitions, listSum p ≤ maxSum) := sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval split_array #[7, 2, 5, 10, 8] 2

/-
info: 9
-/
-- #guard_msgs in
-- #eval split_array #[1, 2, 3, 4, 5] 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval split_array #[1, 4, 4] 3
-- </vc-theorems>