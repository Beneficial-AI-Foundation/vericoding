A palindrome is a word, phrase, number, or other sequence of characters which reads the same backward as forward. Examples of numerical palindromes are: 

* 232
* 110011
* 54322345

Complete the function to test if the given number (`num`) **can be rearranged** to form a numerical palindrome or not. Return a boolean (`true` if it can be rearranged to a palindrome, and `false` if it cannot). Return `"Not valid"` if the input is not an integer or is less than 0.

For this kata, single digit numbers are **NOT** considered numerical palindromes.  

## Examples

```
5        =>  false
2121     =>  true
1331     =>  true 
3357665  =>  true 
1294     =>  false 
"109982" =>  "Not valid"
-42      =>  "Not valid"
```

def palindrome : (n : Int) → String ⊕ Bool := sorry

theorem negative_numbers {n : Int} (h : n < 0) : palindrome n = Sum.inl "Not valid" := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
