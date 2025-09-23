-- <vc-preamble>
def min_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => min x (min_list xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_short (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_short_is_shortest (s : String) :
  find_short s = min_list ((s.split fun c => c = ' ').map String.length)
  := by sorry

theorem find_short_positive (s : String) (h : s ≠ "") :
  find_short s > 0 := by sorry

theorem find_short_not_longer_than_any_word (s : String) (w : String) 
  (h : w ∈ s.split fun c => c = ' ') :
  find_short s ≤ w.length := by sorry

theorem find_short_empty (s : String) :
  s = "" → find_short s = 0 := by sorry  

theorem find_short_single_word (s : String) (h : ¬ s.contains ' ') : 
  find_short s = s.length := by sorry

theorem find_short_two_words (s₁ s₂ : String) :
  find_short (s₁ ++ " " ++ s₂) = min s₁.length s₂.length := by sorry
-- </vc-theorems>