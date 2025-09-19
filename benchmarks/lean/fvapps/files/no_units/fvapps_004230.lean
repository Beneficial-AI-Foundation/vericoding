-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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
-- </vc-definitions>

-- <vc-theorems>
theorem only_letters_full_conversion {s : String} (h₁ : s.length > 0) 
  (h₂ : s.data.all Char.isAlpha) : 
  ((alphabetPosition s).split (· = ' ')).length = s.length := sorry
-- </vc-theorems>