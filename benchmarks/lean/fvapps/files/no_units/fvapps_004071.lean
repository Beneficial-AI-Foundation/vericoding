-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat := sorry

def remove (text : String) (what : Char → Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_length_le_input (text : String) (what : Char → Nat) :
  (remove text what).length ≤ text.length := sorry

theorem remove_preserves_nonremoved_chars (text : String) (what : Char → Nat) (c : Char) :
  what c = 0 → (remove text what).count c = text.count c := sorry

theorem remove_chars_count (text : String) (what : Char → Nat) (c : Char) :
  (remove text what).count c = max 0 (text.count c - what c) := sorry

theorem remove_empty_unchanged (text : String) :
  remove text (fun _ => 0) = text := sorry

theorem remove_repeated_char (n : Nat) (what : Char → Nat) :
  remove (String.mk (List.replicate n 'a')) what = 
    String.mk (List.replicate (max 0 (n - what 'a')) 'a') := sorry
-- </vc-theorems>