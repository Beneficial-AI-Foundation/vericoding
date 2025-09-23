-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hollow_triangle (height : Nat) : List String := sorry

theorem hollow_triangle_height (height : Nat) (h : height > 0) :
  (hollow_triangle height).length = height := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hollow_triangle_width (height : Nat) (h : height > 0) :
  ∀ row ∈ hollow_triangle height, row.length = 2 * height - 1 := sorry

theorem hollow_triangle_bottom_row (height : Nat) (h : height > 0) :
  (hollow_triangle height).getLast (by sorry) = String.mk (List.replicate (2 * height - 1) '#') := sorry

theorem hollow_triangle_symmetric_hashes (height : Nat) (h : height > 0) (i : Nat) :
  ∀ row ∈ hollow_triangle height,
  i < (hollow_triangle height).length - 1 →
  String.contains row (Char.ofNat 35) →
  let chars := row.data
  let leftIdx := chars.findIdx? (· = '#')
  match leftIdx with
  | some l => chars.findIdx? (· = '#') = some ((2 * (height - 1)) - l)
  | none => true := sorry

theorem hollow_triangle_minimal (height : Nat) (h : height = 1) :
  hollow_triangle height = ["#"] := sorry
-- </vc-theorems>