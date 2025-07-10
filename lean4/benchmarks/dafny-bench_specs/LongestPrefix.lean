import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- LongestCommonPrefix: Find the longest common prefix of two character sequences.
    
    Given two sequences of characters, returns the longest prefix that is common
    to both sequences.
    
    Example: LongestCommonPrefix("hello", "help") = "hel"
-/
def longestCommonPrefix (str1 str2 : List Char) : Id (List Char) :=
  let rec loop (i : Nat) (acc : List Char) : List Char :=
    if h : i < min str1.length str2.length then
      if h1 : i < str1.length then
        if h2 : i < str2.length then
          if str1[i] = str2[i] then
            loop (i + 1) (acc ++ [str1[i]])
          else
            acc
        else acc
      else acc
    else
      acc
  loop 0 []

/-- Specification: longestCommonPrefix returns a prefix that is the longest common prefix
    of both input strings.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - The returned prefix is a prefix of both str1 and str2
    - The prefix is maximal (either we reached the end of a string, or the next characters differ)
-/
theorem longestCommonPrefix_spec (str1 str2 : List Char) :
    ⦃⌜True⌝⦄
    longestCommonPrefix str1 str2
    ⦃⇓result => ⌜
      -- prefix is a prefix of str1
      result.length ≤ str1.length ∧ result = str1.take result.length ∧
      -- prefix is a prefix of str2  
      result.length ≤ str2.length ∧ result = str2.take result.length ∧
      -- prefix is maximal
      (result.length = str1.length ∨ result.length = str2.length ∨ 
       (result.length < str1.length ∧ result.length < str2.length ∧
        str1.get? result.length ≠ none ∧ str2.get? result.length ≠ none ∧
        str1.get? result.length ≠ str2.get? result.length))
    ⌝⦄ := by
  sorry