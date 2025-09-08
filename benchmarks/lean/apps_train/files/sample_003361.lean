/-
The Earth has been invaded by aliens. They demand our beer and threaten to destroy the Earth if we do not supply the exact number of beers demanded.

Unfortunately, the aliens only speak Morse code. Write a program to convert morse code into numbers using the following convention:

1 .----
2 ..---
3 ...--
4 ....-
5 .....
6 -....
7 --...
8 ---..
9 ----.
0 -----
-/

def morse_converter (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def convertToMorse (n : Nat) : String :=
  sorry

theorem morse_converter_output_valid (s : String) :
  let result := morse_converter s
  result ≥ 0
  := sorry

/-
info: 11111
-/
-- #guard_msgs in
-- #eval morse_converter ".----.----.----.----.----"

/-
info: 207600
-/
-- #guard_msgs in
-- #eval morse_converter "..----------...-....----------"

/-
info: 1234567890
-/
-- #guard_msgs in
-- #eval morse_converter ".----..---...--....-.....-....--...---..----.-----"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible