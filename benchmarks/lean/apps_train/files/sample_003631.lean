Regex Failure - Bug Fixing #2
Oh no, Timmy's received some hate mail recently but he knows better. Help Timmy fix his regex filter so he can be awesome again!

def filter_words (s : String) : String := sorry 

theorem filter_words_output_is_string (s : String) : 
  filter_words s = filter_words s := sorry

/-- Helper function to count occurrences of a substring -/

def countSubstr (s : String) (sub : String) : Nat := sorry

/-- Helper function to check if a string contains a substring -/

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible