-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greetPerson (firstname : String) (lastname : String) : String := sorry

theorem greet_person_is_string (firstname lastname : String) : 
  greetPerson firstname lastname = greetPerson firstname lastname := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_person_substrings (firstname lastname : String) :
  let result := greetPerson firstname lastname
  ∃ i j k l, (result.drop i).take j = firstname ∧ 
             (result.drop k).take l = lastname := sorry

theorem greet_person_starts_with_hello (firstname lastname : String) :
  (greetPerson firstname lastname).startsWith "Hello" = true := sorry

theorem greet_person_ends_with_python (firstname lastname : String) :
  (greetPerson firstname lastname).endsWith "! You just delved into python." = true := sorry

theorem greet_person_exact_format (firstname lastname : String) :
  greetPerson firstname lastname = s!"Hello {firstname} {lastname}! You just delved into python." := sorry
-- </vc-theorems>