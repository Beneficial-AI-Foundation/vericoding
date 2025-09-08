/-
Write a function that will check whether the permutation of an input string is a palindrome. Bonus points for a solution that is efficient and/or that uses _only_ built-in language functions. Deem yourself **brilliant** if you can come up with a version that does not use _any_ function whatsoever.

# Example 

  `madam` -> True   
  `adamm` -> True   
  `junk`  -> False  

## Hint 
The brute force approach would be to generate _all_ the permutations of the string and check each one of them whether it is a palindrome. However, an optimized approach will not require this at all.
-/

-- <vc-helpers>
-- </vc-helpers>

def permute_a_palindrome (s : String) : Bool := sorry

def String.reverse (s : String) : String := sorry

theorem empty_string_palindrome_permutable :
  permute_a_palindrome "" = true := sorry 

theorem repeat_string_palindrome_permutable (s : String) :
  permute_a_palindrome (s ++ s) = true := sorry

theorem even_length_even_occurrences_palindrome (s : String) :
  let even_str := s ++ s
  permute_a_palindrome even_str = true := sorry

theorem single_char_palindrome_permutable (c : Char) :
  permute_a_palindrome (String.singleton c) = true := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible