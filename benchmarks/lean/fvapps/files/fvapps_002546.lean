-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hamster_me (code : String) (message : String) : String := sorry

theorem hamster_output_contents (code : String) (message : String) (h1 : code ≠ "") :
  let result := hamster_me code message
  ∀ c ∈ result.data, 
    (c ∈ code.data) ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamster_output_length (code : String) (message : String) (h1 : code ≠ "") :
  let result := hamster_me code message
  (result.data.filter Char.isAlpha).length = message.length := sorry

theorem hamster_deterministic (code : String) (message : String) (h1 : code ≠ "") :
  hamster_me code message = hamster_me code message := sorry

theorem hamster_code_order_invariant (code code' : String) (message : String) 
    (h1 : code ≠ "") (h2 : ∀ c, c ∈ code.data ↔ c ∈ code'.data) :
  hamster_me code message = hamster_me code' message := sorry

theorem hamster_empty_message (code : String) (h1 : code ≠ "") :
  hamster_me code "" = "" := sorry

theorem hamster_single_char_code (message : String) :
  let result := hamster_me "a" message
  ∀ c ∈ result.data,
    c = 'a' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := sorry
-- </vc-theorems>