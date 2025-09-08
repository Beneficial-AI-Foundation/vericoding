/-
You have invented a time-machine which has taken you back to ancient Rome. Caeser is impressed with your programming skills and has appointed you to be the new information security officer.

Caeser has ordered you to write a Caeser cipher to prevent Asterix and Obelix from reading his emails.

A Caeser cipher shifts the letters in a message by the value dictated by the encryption key. Since Caeser's emails are very important, he wants all encryptions to have upper-case output, for example:

If key = 3
"hello" -> KHOOR
If key = 7
"hello" -> OLSSV

Input will consist of the message to be encrypted and the encryption key.
-/

-- <vc-helpers>
-- </vc-helpers>

def caeser (message : String) (key : Int) : String := sorry

theorem caeser_preserves_length 
  (message : String) (key : Int) :
  (caeser message key).length = message.length := sorry

theorem caeser_preserves_non_alpha
  (message : String) (key : Int)
  (c1 c2 : Char)
  (h1 : ¬(c1.isAlpha)) :
  c1 = c2 := sorry

theorem caeser_result_uppercase
  (message : String) (key : Int) 
  (c : Char)
  (h1 : c.isAlpha) :
  c.isUpper = true := sorry

theorem caeser_26_is_identity
  (message : String) :
  caeser message 26 = caeser message 0 := sorry

theorem caeser_zero_uppercases
  (message : String) :
  caeser message 0 = 
    String.map (fun c => if c.isAlpha then c.toUpper else c) message := sorry

/-
info: 'THIS IS A MESSAGE'
-/
-- #guard_msgs in
-- #eval caeser "This is a message" 0

/-
info: 'OZG SJW QGM?'
-/
-- #guard_msgs in
-- #eval caeser "who are you?" 18

/-
info: 'ORWJU XWN'
-/
-- #guard_msgs in
-- #eval caeser "final one" 9

-- Apps difficulty: introductory
-- Assurance level: unguarded