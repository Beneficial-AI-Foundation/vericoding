Your users passwords were all stole in the Yahoo! hack, and it turns out they have been lax in creating secure passwords.  Create a function that checks their new password (passed as a string) to make sure it meets the following requirements:

Between 8 - 20 characters

Contains only the following characters: (and at least one character from each category): uppercase letters, lowercase letters, digits, and the special characters !@#$%^&*?

Return "valid" if passed or else "not valid"

def check_password (s : String) : String :=
  sorry

def is_special_char (c : Char) : Bool :=
  sorry

def has_lowercase (s : String) : Bool :=
  sorry 

def has_uppercase (s : String) : Bool :=
  sorry

def has_digit (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded