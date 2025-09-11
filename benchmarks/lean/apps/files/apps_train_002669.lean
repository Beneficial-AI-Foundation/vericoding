-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Position := String

def whose_turn (p : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem position_order_invariant (pos_list : List Position) (h : pos_list.length = 4) :
  ∀ i, i < pos_list.length →
  let shuffled := (pos_list.drop i) ++ (pos_list.take i)
  whose_turn (String.intercalate ";" pos_list) = 
  whose_turn (String.intercalate ";" shuffled) := by sorry

theorem sum_parity (pos_list : List Position) (h : pos_list.length = 4) :
  let pos_str := String.intercalate ";" pos_list
  let ascii_sum := (pos_str.replace ";" "").data.foldl (fun acc c => acc + c.toNat) 0
  whose_turn pos_str = (ascii_sum % 2 = 0) := by sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval whose_turn "b1;g1;b8;g8"

/-
info: False
-/
-- #guard_msgs in
-- #eval whose_turn "c3;g1;b8;g8"

/-
info: False
-/
-- #guard_msgs in
-- #eval whose_turn "f8;h1;f3;c2"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded