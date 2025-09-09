/-
In this kata you will be given an **integer n**, which is the number of times that is thown a coin. You will have to return an array of string for all the possibilities (heads[H] and tails[T]). Examples:
```coin(1) should return {"H", "T"}```
```coin(2) should return {"HH", "HT", "TH", "TT"}```
```coin(3) should return {"HHH", "HHT", "HTH", "HTT", "THH", "THT", "TTH", "TTT"}```
When finished sort them alphabetically.

In C and C++ just return a ```char*``` with all elements separated by```,``` (without space):
```coin(2) should return "HH,HT,TH,TT"```
INPUT:
```0 < n < 18```
Careful with performance!! You'll have to pass 3 basic test (n = 1, n = 2, n = 3), many medium tests (3 < n <= 10) and many large tests (10 < n < 18)
-/

-- <vc-helpers>
-- </vc-helpers>

def coin (n : Nat) : List String := sorry

theorem coin_length (n : Nat) : 
  n ≤ 10 → List.length (coin n) = 2^n := sorry

theorem coin_elem_length (n : Nat) (s : String) :
  n ≤ 10 → s ∈ coin n → String.length s = n := sorry

theorem coin_valid_chars (n : Nat) (s : String) (c : Char) :
  n ≤ 10 → s ∈ coin n → c ∈ s.data → c = 'H' ∨ c = 'T' := sorry

theorem coin_sorted (n : Nat) (i j : Nat) :
  n ≤ 10 → i < j → j < List.length (coin n) → 
  (coin n).get ⟨i, by sorry⟩ ≤ (coin n).get ⟨j, by sorry⟩ := sorry

theorem coin_unique (n : Nat) :
  n ≤ 10 → List.Nodup (coin n) := sorry

theorem coin_empty :
  coin 0 = [""] := sorry

theorem coin_negative (n : Int) :
  n < 0 → coin (Int.toNat n) = [] := sorry

/-
info: ['H', 'T']
-/
-- #guard_msgs in
-- #eval coin 1

/-
info: ['HH', 'HT', 'TH', 'TT']
-/
-- #guard_msgs in
-- #eval coin 2

/-
info: ['HHH', 'HHT', 'HTH', 'HTT', 'THH', 'THT', 'TTH', 'TTT']
-/
-- #guard_msgs in
-- #eval coin 3

-- Apps difficulty: introductory
-- Assurance level: unguarded