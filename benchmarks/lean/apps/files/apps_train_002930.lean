/-
Most of this problem is by the original author of [the harder kata](https://www.codewars.com/kata/556206664efbe6376700005c), I just made it simpler.

I read a book recently, titled "Things to Make and Do in the Fourth Dimension" by comedian and mathematician Matt Parker ( [Youtube](https://www.youtube.com/user/standupmaths) ), and in the first chapter of the book Matt talks about problems he likes to solve in his head to take his mind off the fact that he is in his dentist's chair, we've all been there!

The problem he talks about relates to polydivisible numbers, and I thought a kata should be written on the subject as it's quite interesting. (Well it's interesting to me, so there!)

### Polydivisib... huh what?

So what are they?

A polydivisible number is divisible in an unusual way. The first digit is cleanly divisible by `1`, the first two digits are cleanly divisible by `2`, the first three by `3`, and so on.

### Examples

Let's take the number `1232` as an example.
```
1     / 1 = 1     // Works
12    / 2 = 6     // Works
123   / 3 = 41    // Works
1232  / 4 = 308   // Works
```
`1232` is a polydivisible number.

However, let's take the number `123220` and see what happens.
```
 1      /1 = 1    // Works
 12     /2 = 6    // Works
 123    /3 = 41   // Works
 1232   /4 = 308  // Works
 12322  /5 = 2464.4         // Doesn't work
 123220 /6 = 220536.333...  // Doesn't work
```
`123220` is not polydivisible.

### Your job: check if a number is polydivisible or not.

Return `true` if it is, and `false` if it isn't.

Note: All inputs will be valid numbers between `0` and `2^53-1 (9,007,199,254,740,991)` (inclusive).   
Note: All single digit numbers (including `0`) are trivially polydivisible.
Note: Except for `0`, no numbers will start with `0`.
-/

def polydivisible (n : Nat) : Bool := sorry

def digits (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def take_prefix (n : Nat) (len : Nat) : Nat := sorry

theorem polydivisible_characterization {n : Nat} :
  polydivisible n ↔ 
  (∀ i : Nat, i > 0 ∧ i ≤ (digits n).length → 
    take_prefix n i % i = 0) := sorry

theorem single_digit_polydivisible {n : Nat} :
  n > 0 ∧ n < 10 → polydivisible n := sorry

theorem polydivisible_positive {n : Int} :
  n ≤ 0 → polydivisible n.toNat = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval polydivisible 1232

/-
info: False
-/
-- #guard_msgs in
-- #eval polydivisible 123220

/-
info: True
-/
-- #guard_msgs in
-- #eval polydivisible 987654

-- Apps difficulty: introductory
-- Assurance level: unguarded