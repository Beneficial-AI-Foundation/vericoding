-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode (code : List Nat) (key : Nat) : String := sorry

theorem decode_type_and_bounds {code : List Nat} {key : Nat} 
  (h1 : ∀ x ∈ code, 1 ≤ x ∧ x ≤ 26)
  (h2 : 1 ≤ key ∧ key ≤ 9999)
  (h3 : code.length > 0) :
  ∃ result : String,
    (result.length = code.length) ∧ 
    (∀ c ∈ result.data, 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_wrapping (key : Nat) 
  (h : 1 ≤ key ∧ key ≤ 9999) :
  ∀ n : Nat,
    (decode (List.replicate n 1) key).length = n := sorry

theorem decode_key_zero_equiv {code : List Nat}
  (h1 : ∀ x ∈ code, 1 ≤ x ∧ x ≤ 26)
  (h2 : code.length > 0) :
  decode code 0 = decode code 10000 := sorry

/-
info: 'scout'
-/
-- #guard_msgs in
-- #eval decode [20, 12, 18, 30, 21] 1939

/-
info: 'masterpiece'
-/
-- #guard_msgs in
-- #eval decode [14, 10, 22, 29, 6, 27, 19, 18, 6, 12, 8] 1939
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded