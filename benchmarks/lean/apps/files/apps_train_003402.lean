-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def original_number (s : String) : String := sorry

def generate_number_word (c : Char) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digits_theorem {n : Nat} (h : n ≤ 9) : 
  let word := generate_number_word (Char.ofNat (n + 48))
  let scrambled := String.mk (List.reverse (word.data))
  original_number scrambled = String.mk [Char.ofNat (n + 48)] := sorry

theorem multi_digits_theorem {nums : List Nat} (h : ∀ n ∈ nums, n ≤ 9) :
  let words := List.map (fun n => generate_number_word (Char.ofNat (n + 48))) nums
  let combined := String.join words
  let scrambled := String.mk (List.reverse combined.data)
  original_number scrambled = 
    String.join (List.map (fun n => String.mk [Char.ofNat (n + 48)]) nums) := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval original_number "ONE"

/-
info: '1'
-/
-- #guard_msgs in
-- #eval original_number "OEN"

/-
info: '12'
-/
-- #guard_msgs in
-- #eval original_number "ONETWO"

/-
info: '12'
-/
-- #guard_msgs in
-- #eval original_number "OONETW"

/-
info: '123'
-/
-- #guard_msgs in
-- #eval original_number "TTONWOHREEE"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded