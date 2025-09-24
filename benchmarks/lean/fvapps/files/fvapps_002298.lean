-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_long_pressed_name (name typed : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem always_accepts_repeated_chars 
  (name typed : String) 
  (h : ∀ (i : Nat), i < name.length → typed.length ≥ name.length) :
  is_long_pressed_name name typed = true :=
sorry

theorem length_property
  (name typed : String)
  (h : is_long_pressed_name name typed = true) :
  typed.length ≥ name.length :=
sorry

theorem identical_strings_property
  (s : String) :
  is_long_pressed_name s s = true :=
sorry

theorem empty_typed_property
  (name typed : String)
  (h1 : typed.length = 0)
  (h2 : name.length > 0) :
  is_long_pressed_name name typed = false :=
sorry

theorem deletion_property
  (s : String)
  (h : s.length > 0)
  (i : Nat)
  (hi : i < s.length) :
  let deleted := s.data.take i ++ s.data.drop (i+1)
  is_long_pressed_name s (String.mk deleted) = false :=
sorry
-- </vc-theorems>