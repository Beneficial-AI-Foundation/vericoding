/-
Here we have a function that help us spam our hearty laughter. But is not working! I need you to find out why...

Expected results:

```python
spam(1)  ==> "hue"
spam(6)  ==> "huehuehuehuehuehue"
spam(14) ==> "huehuehuehuehuehuehuehuehuehuehuehuehuehue"
```
-/

def String.replicate (n : Nat) (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def spam (n : Nat) : String :=
  sorry

theorem spam_multiplication (n : Nat) : n ≤ 1000 → spam n = String.replicate n "hue" :=
  sorry

/-
info: 'hue'
-/
-- #guard_msgs in
-- #eval spam 1

/-
info: 'huehuehuehuehuehue'
-/
-- #guard_msgs in
-- #eval spam 6

/-
info: 'huehuehuehuehuehuehuehuehuehuehuehuehuehue'
-/
-- #guard_msgs in
-- #eval spam 14

-- Apps difficulty: introductory
-- Assurance level: unguarded