/-
You probably know the 42 number as "The answer to life, the universe and everything" according to Douglas Adams' "The Hitchhiker's Guide to the Galaxy". For Freud, the answer was quite different.

In the society he lived in, people-women in particular- had to repress their sexual needs and desires. This was simply how the society was at the time. 
Freud then wanted to study the illnesses created by this, and so he digged to the root of their desires. This led to some of the most important psychoanalytic theories to this day, Freud being the father of psychoanalysis.

Now, basically, when a person hears about Freud, s/he hears "sex" because for Freud, everything was basically related to, and explained by sex. 

In this kata, the toFreud() function will take a string as its argument, and return a string with every word replaced by the explanation to everything, according to Freud. Note that an empty string, or no arguments, should result in the ouput being ""(empty string).
-/

def split (s : String) (sep : Char → Bool) : List String := sorry
def trim (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def to_freud (s : String) : String := sorry

theorem empty_string_returns_empty :
  to_freud "" = "" := sorry

theorem only_whitespace_returns_empty (s : String) :
  trim s = "" → to_freud s = "" := sorry

theorem non_empty_only_contains_sex (s : String) :
  trim s ≠ "" →
  List.all (split (to_freud s) (· = ' ')) (· = "sex") := sorry

theorem preserves_word_count (s : String) :
  trim s ≠ "" →
  (split (to_freud s) (· = ' ')).length = (split (trim s) (· = ' ')).length := sorry

/-
info: 'sex'
-/
-- #guard_msgs in
-- #eval to_freud "test"

/-
info: 'sex sex sex sex'
-/
-- #guard_msgs in
-- #eval to_freud "This is a test"

/-
info: ''
-/
-- #guard_msgs in
-- #eval to_freud ""

-- Apps difficulty: introductory
-- Assurance level: unguarded