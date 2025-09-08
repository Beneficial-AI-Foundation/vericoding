/-
Born a misinterpretation of [this kata](https://www.codewars.com/kata/simple-fun-number-334-two-beggars-and-gold/), your task here is pretty simple: given an array of values and an amount of beggars, you are supposed to return an array with the sum of what each beggar brings home, assuming they all take regular turns, from the first to the last.

For example: `[1,2,3,4,5]` for `2` beggars will return a result of `[9,6]`, as the first one takes `[1,3,5]`, the second collects `[2,4]`.

The same array with `3` beggars would have in turn have produced a better out come for the second beggar: `[5,7,3]`, as they will respectively take `[1,4]`, `[2,5]` and `[3]`.

Also note that not all beggars have to take the same amount of "offers", meaning that the length of the array is not necessarily a multiple of `n`; length can be even shorter, in which case the last beggars will of course take nothing (`0`).

***Note:*** in case you don't get why this kata is about *English* beggars, then you are not familiar on how religiously queues are taken in the kingdom ;)
-/

def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

def beggars (values : List Int) (n : Nat) : List Int := sorry

def getNth (values : List Int) (n i : Nat) : Int :=
  match values with
  | [] => 0
  | x::xs => if i % n = 0 then x + getNth xs n (i+1) else getNth xs n (i+1)

theorem beggars_empty_for_zero_n 
  (values : List Int) :
  beggars values 0 = [] := sorry

theorem beggars_length_property 
  (values : List Int) (n : Nat) : 
  n > 0 → (beggars values n).length = n := sorry 

theorem beggars_sum_property 
  (values : List Int) (n : Nat) :
  n > 0 → List.sum values = List.sum (beggars values n) := sorry

theorem beggars_single_beggar_property
  (values : List Int) :
  values.length > 0 → beggars values 1 = [List.sum values] := sorry

theorem beggars_more_beggars_property
  (values : List Int) (n : Nat) :
  n > values.length →
  beggars values n = 
    beggars values values.length ++ List.replicate (n - values.length) 0 := sorry

/-
info: [15]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 1

/-
info: [9, 6]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 2

/-
info: [5, 7, 3]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 3

-- Apps difficulty: introductory
-- Assurance level: guarded