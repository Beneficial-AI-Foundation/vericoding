-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def norm_index_test {α : Type} [Inhabited α] (s : List α) (i : Int) : Option α := sorry 

theorem norm_index_empty_sequence {α : Type} [Inhabited α] (i : Int) :
  @norm_index_test α _ [] i = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem norm_index_nonempty_sequence {α : Type} [Inhabited α] (s : List α) (i : Int) :
  s ≠ [] → @norm_index_test α _ s i = some (s.get! (Int.toNat (Int.mod i s.length))) := sorry

theorem norm_index_wrapping {α : Type} [Inhabited α] (s : List α) (i : Int) :
  s ≠ [] → 
  @norm_index_test α _ s i = @norm_index_test α _ s (i + s.length) ∧ 
  @norm_index_test α _ s i = @norm_index_test α _ s (i - s.length) := sorry

theorem norm_index_identity {α : Type} [Inhabited α] (s : List α) :
  s ≠ [] →
  ∀ i : Nat, i < s.length → @norm_index_test α _ s i = some (s.get! i) := sorry

theorem norm_index_negative {α : Type} [Inhabited α] (s : List α) :
  s ≠ [] →
  ∀ i : Nat, i < s.length → 
  @norm_index_test α _ s (-i-1) = some (s.get! (s.length - i - 1)) := sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval norm_index_test [] 10

/-
info: 1
-/
-- #guard_msgs in
-- #eval norm_index_test [1, 2, 3] 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval norm_index_test test_seq 4

/-
info: 1
-/
-- #guard_msgs in
-- #eval norm_index_test test_seq 6

/-
info: 3
-/
-- #guard_msgs in
-- #eval norm_index_test test_seq -1

/-
info: 3
-/
-- #guard_msgs in
-- #eval norm_index_test test_seq -4

/-
info: 1
-/
-- #guard_msgs in
-- #eval norm_index_test test_seq -6
-- </vc-theorems>