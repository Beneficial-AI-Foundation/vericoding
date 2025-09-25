-- <vc-preamble>
def KEYBOARD := "abcde123fghij456klmno789pqrst.@0uvwxyz_/"

def manhattan (p1 p2 : Nat × Nat) : Nat := 
  let (x1, y1) := p1
  let (x2, y2) := p2
  Nat.sub (if x2 ≥ x1 then x2 else x1) (if x2 ≥ x1 then x1 else x2) + 
  Nat.sub (if y2 ≥ y1 then y2 else y1) (if y2 ≥ y1 then y1 else y2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tv_remote (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tv_remote_min_length (s : String) :
  tv_remote s ≥ s.length := by
  sorry

theorem tv_remote_nonnegative (s : String) :
  tv_remote s ≥ 0 := by
  sorry

theorem tv_remote_empty :
  tv_remote "" = 0 := by
  sorry

theorem tv_remote_repeat_chars (c : Char) (n : Nat) :
  tv_remote (String.mk (List.replicate n c)) = 
    n + manhattan (0, 0) (0, 0) := by
  sorry

theorem tv_remote_substring_cost (s : String) (h : s.length ≥ 2) :
  tv_remote (String.dropRight s 1) < tv_remote s := by
  sorry
-- </vc-theorems>