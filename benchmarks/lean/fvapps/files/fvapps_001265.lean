-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (n : Nat) : List String := sorry 

def String.countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_length (n : Nat) (h : n > 0) :
  (generate_pattern n).length = n := sorry

theorem pattern_first_line (n : Nat) (h : n > 0) :
  (generate_pattern n).head! = String.join (List.map toString (List.range' n n 1)) := sorry

theorem pattern_stars_increment (n : Nat) (h : n > 0) (i : Fin n) : 
  let len_eq := pattern_length n h
  ((generate_pattern n).get ⟨i.val, by rw [len_eq]; exact i.isLt⟩).countChar '*' = i.val := sorry

theorem pattern_stars_prefix (n : Nat) (h : n > 0) (i : Fin n) :
  let len_eq := pattern_length n h
  ((generate_pattern n).get ⟨i.val, by rw [len_eq]; exact i.isLt⟩).startsWith (String.mk (List.replicate i.val '*')) := sorry
-- </vc-theorems>