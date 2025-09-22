-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encryptor (key : Int) (message : String) : String := sorry

theorem encryptor_preserves_length (key : Int) (message : String) :
  (encryptor key message).length = message.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encryptor_inverse (key : Int) (message : String) :
  encryptor (-key) (encryptor key message) = message := sorry

theorem encryptor_key_wrapping (key : Int) (message : String) :
  encryptor key message = encryptor (key % 26) message := sorry

theorem encryptor_preserves_non_letters (key : Int) (message : String) :
  let nonLetters (s : String) := s.foldl (fun acc c => if c.isAlpha then acc else acc.push c) ""
  nonLetters message = nonLetters (encryptor key message) := sorry

theorem encryptor_identity_keys (message : String) :
  encryptor 0 message = message ∧ encryptor 26 message = message := sorry
-- </vc-theorems>