/-
Tired of those repetitive javascript challenges? Here's a unique hackish one that should keep you busy for a while ;)

There's a mystery function which is already available for you to use. It's a simple function called `mystery`. It accepts a string as a parameter and outputs a string. The exercise depends on guessing what this function actually does.

You can call the mystery function like this:

```python
my_output = mystery("my_input")
```

Using your own test cases, try to call the mystery function with different input strings and try to analyze its output in order to guess what is does. You are free to call the mystery function in your own test cases however you want.

When you think you've understood how my mystery function works, prove it by reimplementing its logic in a function that you should call 'solved(x)'. To validate your code, your function 'solved' should return the same output as my function 'mystery' given the same inputs.

Beware! Passing your own test cases doesn't imply you'll pass mine.

Cheaters are welcome :)

Have fun!

---

Too easy? Then this kata will totally blow your mind:

http://www.codewars.com/kata/mystery-function-number-2
-/

def sorted (s : String) : Bool := 
  let chars := s.data
  chars.zip (chars.drop 1) |>.all (fun (a, b) => a ≤ b)

-- <vc-helpers>
-- </vc-helpers>

def solved (s : String) : String := sorry

theorem solved_returns_sorted (s : String) :
  sorted (solved s) = true := sorry

theorem solved_maintains_even_length (s : String) :
  s.length % 2 = 0 → (solved s).length = s.length := sorry

theorem solved_reduces_odd_length (s : String) :
  s.length % 2 = 1 → (solved s).length = s.length - 1 := sorry

theorem solved_maintains_character_set (s : String) :
  ∀ c ∈ (solved s).data, c ∈ s.data := sorry

theorem solved_reduces_char_set_odd (s : String) :
  s.length % 2 = 1 → (solved s).length = s.length - 1 ∧ 
  (∀ c ∈ (solved s).data, c ∈ s.data) := sorry

theorem solved_idempotent (s : String) :
  solved (solved s) = solved s := sorry

/-
info: 'abcd'
-/
-- #guard_msgs in
-- #eval solved "abcd"

/-
info: 'abde'
-/
-- #guard_msgs in
-- #eval solved "bacde"

/-
info: 'abcd'
-/
-- #guard_msgs in
-- #eval solved "dcba"

-- Apps difficulty: introductory
-- Assurance level: unguarded