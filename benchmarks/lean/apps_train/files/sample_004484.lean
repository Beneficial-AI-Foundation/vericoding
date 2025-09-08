/-
## The Riddle

The King of a small country invites 1000 senators to his annual party. As a tradition, each senator brings the King a bottle of wine. Soon after, the Queen discovers that one of the senators is trying to assassinate the King by giving him a bottle of poisoned wine. Unfortunately, they do not know which senator, nor which bottle of wine is poisoned, and the poison is completely indiscernible.

However, the King has 10 lab rats. He decides to use them as taste testers to determine which bottle of wine contains the poison. The poison when taken has no effect on the rats, until exactly 24 hours later when the infected rats suddenly die. The King needs to determine which bottle of wine is poisoned by tomorrow, so that the festivities can continue as planned.

Hence he only has time for one round of testing, he decides that each rat tastes multiple bottles, according to a certain scheme.

## Your Task

You receive an array of integers (`0 to 9`), each of them is the number of a rat which died after tasting the wine bottles. Return the number of the bottle (`1..1000`) which is poisoned.

**Good Luck!**

*Hint: think of rats as a certain representation of the number of the bottle...*
-/

def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + xs.sum

-- <vc-helpers>
-- </vc-helpers>

def find (rats : List Nat) : Nat := sorry

theorem find_total_is_sum_of_powers (rats : List Nat) 
  (h : ∀ x, x ∈ rats → x ≤ 9) 
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0)
  (h4 : (rats.map (fun r => 2^r)).sum ≤ 1000) :
  find rats = (rats.map (fun r => 2^r)).sum := sorry

theorem find_binary_representation (rats : List Nat)
  (h : ∀ x, x ∈ rats → x ≤ 9)
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0) :
  ∀ i, i ≤ 9 → 
    (if i ∈ rats 
     then (find rats).mod (2^(i+1)) ≥ 2^i
     else (find rats).mod (2^(i+1)) < 2^i) := sorry

theorem find_commutative (rats : List Nat)
  (h : ∀ x, x ∈ rats → x ≤ 9)
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0) :
  find rats = find rats.reverse := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find [0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find [1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find [2]

/-
info: 1000
-/
-- #guard_msgs in
-- #eval find [3, 5, 6, 7, 8, 9]

/-
info: 27
-/
-- #guard_msgs in
-- #eval find [0, 1, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded