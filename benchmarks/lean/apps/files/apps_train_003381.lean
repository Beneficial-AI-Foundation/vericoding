-- <vc-preamble>
def solve (text : String) (k : Nat) : String := sorry

def get_char_indices (s : String) (c : Char) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sorted (l : List Nat) : Prop := 
  ∀ i j, i < j → j < l.length → 
  match l.get? i, l.get? j with
  | some vi, some vj => vi ≤ vj
  | _, _ => True
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_length (text : String) (k : Nat) (h : text.length > 0) :
  (solve text k).length = max 0 (text.length - min k text.length) := sorry

theorem solve_chars_from_original (text : String) (k : Nat) (h : text.length > 0) :
  ∀ c, c ∈ (solve text k).data → c ∈ text.data := sorry

theorem solve_maintains_order (text : String) (k : Nat) (h : text.length > 0) :
  ∀ c, c ∈ (solve text k).data →
    let result_indices := get_char_indices (solve text k) c
    let orig_indices := get_char_indices text c
    List.sorted result_indices := sorry

theorem solve_k_zero (text : String) (h : text.length > 0) :
  solve text 0 = text := sorry

theorem solve_k_length (text : String) (h : text.length > 0) :
  solve text text.length = "" := sorry

/-
info: 'bracadabra'
-/
-- #guard_msgs in
-- #eval solve "abracadabra" 1

/-
info: 'rcdbr'
-/
-- #guard_msgs in
-- #eval solve "abracadabra" 6

/-
info: 'cccbbabaccbc'
-/
-- #guard_msgs in
-- #eval solve "cccaabababaccbc" 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded