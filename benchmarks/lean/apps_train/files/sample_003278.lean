/-
Description overhauled by V

---

I've invited some kids for my son's birthday, during which I will give to each kid some amount of candies.

Every kid hates receiving less amount of candies than any other kids, and I don't want to have any candies left - giving it to my kid would be bad for his teeth.

However, not every kid invited will come to my birthday party.

What is the minimum amount of candies I have to buy, so that no matter how many kids come to the party in the end, I can still ensure that each kid can receive the same amount of candies, while leaving no candies left?

It's ensured that at least one kid will participate in the party.
-/

-- <vc-helpers>
-- </vc-helpers>

def candies_to_buy (n : Nat) : Nat := sorry

theorem candies_to_buy_properties (n : Nat) (h : n > 0 ∧ n ≤ 20) : 
  let result := candies_to_buy n
  -- Result greater than or equal to n
  result ≥ n ∧ 
  -- Result evenly divisible by all numbers 1 to n
  (∀ i, 1 ≤ i ∧ i ≤ n → result % i = 0) ∧
  -- Result is positive
  result > 0 := sorry

theorem candies_to_buy_minimum : candies_to_buy 1 = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval candies_to_buy 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval candies_to_buy 2

/-
info: 60
-/
-- #guard_msgs in
-- #eval candies_to_buy 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible