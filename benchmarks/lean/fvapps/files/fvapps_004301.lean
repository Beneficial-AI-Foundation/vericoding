-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort (xs : List α) (lt : α → α → Bool) : List α := sorry

def reverse_fun (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preserved (s : String) : 
  (reverse_fun s).length = s.length := sorry

theorem same_character_set (s : String) :
  sort (reverse_fun s).data (· ≤ ·) = sort s.data (· ≤ ·) := sorry

theorem not_idempotent (s : String) :
  s.length > 1 → reverse_fun (reverse_fun s) ≠ reverse_fun s := sorry

theorem single_char_invariant (s : String) :
  s.length ≤ 1 → reverse_fun s = s := sorry

theorem first_char_movement (s : String) (h : s.length > 1) :
  (reverse_fun s).get 0 ≠ s.get 0 := sorry
-- </vc-theorems>