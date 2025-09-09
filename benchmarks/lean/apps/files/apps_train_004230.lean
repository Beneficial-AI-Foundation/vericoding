-- <vc-helpers>
-- </vc-helpers>

def alphabetPosition (s : String) : String := sorry

theorem output_matches_input_letters (s : String) :
  let result := alphabetPosition s
  let inputLetters := s.data.filter Char.isAlpha
  if inputLetters = [] then
    result = ""
  else
    let outputNums := (result.split (· = ' '))
    outputNums.length = inputLetters.length ∧
    (List.zip inputLetters outputNums).all (fun (letter, num) => 
      match num.toNat? with
      | some n => n = letter.toLower.toNat - 96
      | none => false) := sorry

theorem only_letters_full_conversion {s : String} (h₁ : s.length > 0) 
  (h₂ : s.data.all Char.isAlpha) : 
  ((alphabetPosition s).split (· = ' ')).length = s.length := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval alphabet_position "The sunset sets at twelve o" clock."

/-
info: expected2
-/
-- #guard_msgs in
-- #eval alphabet_position "-.-""

/-
info: expected3
-/
-- #guard_msgs in
-- #eval alphabet_position "aBc"

-- Apps difficulty: introductory
-- Assurance level: unguarded