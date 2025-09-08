/-
As you may know, once some people pass their teens, they jokingly only celebrate their 20th or 21st birthday, forever. With some maths skills, that's totally possible - you only need to select the correct number base!

For example, if they turn 32, that's exactly 20 - in base 16... Already 39? That's just 21, in base 19!

Your task is to translate the given age to the much desired 20 (or 21) years, and indicate the number base, in the format specified below.

**Note:** input will be always > 21

### Examples:

```
32  -->  "32? That's just 20, in base 16!"
39  -->  "39? That's just 21, in base 19!"
```

*Hint: if you don't know (enough) about [numeral systems](https://en.wikipedia.org/wiki/Numeral_system) and [radix](https://en.wikipedia.org/wiki/Radix), just observe the pattern!*

---

## My other katas

If you enjoyed this kata then please try [my other katas](https://www.codewars.com/collections/katas-created-by-anter69)! :-)

---

### *Translations are welcome!*
-/

-- <vc-helpers>
-- </vc-helpers>

def womens_age (n : Nat) : String := sorry

theorem womens_age_starts_with (n : Nat) (h : n ≥ 2) : 
  (womens_age n).startsWith s!"{n}? That's just" = true := sorry

theorem womens_age_ends_with (n : Nat) (h : n ≥ 2) :
  (womens_age n).endsWith "!" = true := sorry

theorem womens_age_value_20_or_21 (n : Nat) (h : n ≥ 2) :
  let val := String.toNat! ((womens_age n).split (· == ' ') |>.get! 3)
  val = 20 ∨ val = 21 := sorry

theorem womens_age_base_is_div2 (n : Nat) (h : n ≥ 2) :
  let base := String.toNat! ((womens_age n).split (· == ' ') |>.get! 5)
  base = n / 2 := sorry

theorem womens_age_even_20_odd_21 (n : Nat) (h : n ≥ 2) :
  let val := String.toNat! ((womens_age n).split (· == ' ') |>.get! 3)
  (n % 2 = 0 → val = 20) ∧ (n % 2 = 1 → val = 21) := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded