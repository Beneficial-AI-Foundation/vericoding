/-
Caesar Ciphers are one of the most basic forms of encryption. It consists of a message and a key, and it shifts the letters of the message for the value of the key. 

Read more about it here: https://en.wikipedia.org/wiki/Caesar_cipher

## Your task

Your task is to create a function encryptor that takes 2 arguments - key and message - and returns the encrypted message.

Make sure to only shift letters, and be sure to keep the cases of the letters the same. All punctuation, numbers, spaces, and so on should remain the same. 

Also be aware of keys greater than 26 and less than -26. There's only 26 letters in the alphabet!

## Examples

A message `'Caesar Cipher'` and a key of `1` returns `'Dbftbs Djqifs'`.

A message `'Caesar Cipher'` and a key of `-1` returns `'Bzdrzq Bhogdq'`.
-/

-- <vc-helpers>
-- </vc-helpers>

def encryptor (key : Int) (message : String) : String := sorry

theorem encryptor_preserves_length (key : Int) (message : String) :
  (encryptor key message).length = message.length := sorry

theorem encryptor_inverse (key : Int) (message : String) :
  encryptor (-key) (encryptor key message) = message := sorry

theorem encryptor_key_wrapping (key : Int) (message : String) :
  encryptor key message = encryptor (key % 26) message := sorry

theorem encryptor_preserves_non_letters (key : Int) (message : String) :
  let nonLetters (s : String) := s.foldl (fun acc c => if c.isAlpha then acc else acc.push c) ""
  nonLetters message = nonLetters (encryptor key message) := sorry

theorem encryptor_identity_keys (message : String) :
  encryptor 0 message = message ∧ encryptor 26 message = message := sorry

/-
info: 'Dbftbs Djqifs'
-/
-- #guard_msgs in
-- #eval encryptor 1 "Caesar Cipher"

/-
info: 'Bzdrzq Bhogdq'
-/
-- #guard_msgs in
-- #eval encryptor -1 "Caesar Cipher"

/-
info: 'Khoor, Zruog 123!'
-/
-- #guard_msgs in
-- #eval encryptor 3 "Hello, World 123!"

-- Apps difficulty: introductory
-- Assurance level: unguarded