-- <vc-preamble>
def matrixfy (s : String) : String ⊕ (List (List Char)) := sorry 

theorem matrixfy_empty_input (s : String) : 
  s.length = 0 → matrixfy s = Sum.inl "name must be at least one letter" := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getSideLength (n : Nat) : Nat :=
  let sqrt := Float.sqrt (Float.ofNat n)
  let ceil := Float.ceil sqrt
  ceil.toUInt64.toNat
-- </vc-definitions>

-- <vc-theorems>
theorem matrixfy_square_matrix (s : String) :
  s.length > 0 → 
  match matrixfy s with
  | Sum.inr matrix => ∃ n, matrix.length = n ∧ matrix.all (fun row => row.length = n) 
  | _ => False
  := sorry

theorem matrixfy_size (s : String) :
  s.length > 0 →
  match matrixfy s with
  | Sum.inr matrix => matrix.length = getSideLength s.length
  | _ => False
  := sorry

theorem matrixfy_preserves_string (s : String) :
  s.length > 0 →
  match matrixfy s with
  | Sum.inr matrix => 
    let flattened := matrix.join.asString
    flattened.take s.length = s ∧
    (flattened.drop s.length).all (· = '.')
  | _ => False
  := sorry

theorem matrixfy_single_chars (s : String) :
  s.length > 0 →
  match matrixfy s with
  | Sum.inr matrix => matrix.all (fun row => row.all (fun _ => true))
  | _ => False
  := sorry

/-
info: 'name must be at least one letter'
-/
-- #guard_msgs in
-- #eval matrixfy ""

/-
info: [['G']]
-/
-- #guard_msgs in
-- #eval matrixfy "G"

/-
info: [['F', 'r', 'a'], ['n', 'k', '.'], ['.', '.', '.']]
-/
-- #guard_msgs in
-- #eval matrixfy "Frank"
-- </vc-theorems>