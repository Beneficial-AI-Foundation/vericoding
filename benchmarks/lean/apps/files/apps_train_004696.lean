-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (n : Nat) (s : String) : String := sorry
def decode (s : String) : String := sorry

/- For any number n and text, decoding after encoding returns original text -/
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip (n : Nat) (text : String) :
  decode (encode n text) = text := sorry 

/- The first word of encoded text equals the input number n as string -/  

theorem encode_starts_with_n (n : Nat) (text : String) : 
  List.get! (String.splitOn (encode n text) " ") 0 = toString n := sorry

/- Empty string cases -/

theorem empty_string_case1 : decode (encode 5 "") = "" := sorry
theorem empty_string_case2 : encode 0 "" = "0 " := sorry

/-
info: solution
-/
-- #guard_msgs in
-- #eval encode 10 "If you wish to make an apple pie from scratch, you must first invent the universe."

/-
info: quote
-/
-- #guard_msgs in
-- #eval decode encode(10, quote)

/-
info: test2
-/
-- #guard_msgs in
-- #eval decode encode(3, test2)

/-
info: test3
-/
-- #guard_msgs in
-- #eval decode encode(5, test3)
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded