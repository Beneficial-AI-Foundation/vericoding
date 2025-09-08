/-
This challenge extends the previous [repeater()](https://www.codewars.com/kata/thinkful-string-drills-repeater) challenge. Just like last time, your job is to write a function that accepts a string and a number as arguments. This time, however, you should format the string you return like this:
```python
>>> repeater('yo', 3)
'"yo" repeated 3 times is: "yoyoyo"'
>>> repeater('WuB', 6)
'"WuB" repeated 6 times is: "WuBWuBWuBWuBWuBWuB"'
```
-/

-- <vc-helpers>
-- </vc-helpers>

def String.repeat (s : String) (n : Nat) : String := sorry

def repeater (s : String) (n : Nat) : String := sorry

theorem repeater_format_match (s : String) (n : Nat) (h : s.length > 0) :
  repeater s n = "\"" ++ s ++ "\" repeated " ++ toString n ++ " times is: \"" ++ (String.repeat s n) ++ "\"" := sorry

theorem repeater_length (s : String) (n : Nat) (h : s.length > 0) :
  (repeater s n).length = 
    s.length * n + ("\" repeated " ++ toString n ++ " times is: \"\"").length := sorry

theorem repeater_zero_empty_result (s : String) :
  ∃ (p : String), repeater s 0 = p ++ "\"\"" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded