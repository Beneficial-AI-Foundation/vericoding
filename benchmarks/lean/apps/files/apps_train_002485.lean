/-
=====Example=====
In Python, a string can be split on a delimiter.

Example:
>>> a = "this is a string"
>>> a = a.split(" ") # a is converted to a list of strings. 
>>> print a
['this', 'is', 'a', 'string']

Joining a string is simple:

>>> a = "-".join(a)
>>> print a
this-is-a-string 

=====Problem Statement=====
You are given a string. Split the string on a " " (space) delimiter and join using a - hyphen.

=====Input Format=====
The first line contains a string consisting of space separated words.

=====Output Format=====
 Print the formatted string as explained above.
-/

-- <vc-helpers>
-- </vc-helpers>

def hyphenJoin (s : String) : String := sorry

theorem hyphen_join_word_count {words : List String} 
  (h1 : ∀ w ∈ words, w.length > 0) 
  (h2 : words.length > 0) :
  let input := String.join (List.intersperse " " words)
  let result := hyphenJoin input
  (result.splitOn "-").length = words.length ∧ 
  (result.splitOn "-") = words := 
sorry

theorem hyphen_join_whitespace_empty (s : String)
  (h : ∀ c ∈ s.data, c.isWhitespace) :
  hyphenJoin s = "" :=
sorry

theorem hyphen_join_basic_properties (s : String) 
  (h : s.length > 0) :
  let result := hyphenJoin s
  (¬ ∃ c ∈ result.data, c = ' ') ∧ 
  (s.trim ≠ "" → ((∃ c ∈ result.data, c = '-') ∨ (s.splitOn " ").length = 1)) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded