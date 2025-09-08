/-
Write a comparator for a list of phonetic words for the letters of the [greek alphabet](https://en.wikipedia.org/wiki/Greek_alphabet).

A comparator is:
> *a custom comparison function of two arguments (iterable elements) which should return a negative, zero or positive number depending on whether the first argument is considered smaller than, equal to, or larger than the second argument*

*(source: https://docs.python.org/2/library/functions.html#sorted)*

The greek alphabet is preloded for you as `greek_alphabet`:

```python
greek_alphabet = (
    'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 
    'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 
    'nu', 'xi', 'omicron', 'pi', 'rho', 'sigma',
    'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega')
```

## Examples

```python
greek_comparator('alpha', 'beta')   <  0
greek_comparator('psi', 'psi')      == 0
greek_comparator('upsilon', 'rho')  >  0
```
-/

def greek_index (l : GreekLetter) : Nat :=
  match l with
  | .alpha => 0 | .beta => 1 | .gamma => 2 | .delta => 3
  | .epsilon => 4 | .zeta => 5 | .eta => 6 | .theta => 7
  | .iota => 8 | .kappa => 9 | .lambda => 10 | .mu => 11
  | .nu => 12 | .xi => 13 | .omicron => 14 | .pi => 15
  | .rho => 16 | .sigma => 17 | .tau => 18 | .upsilon => 19
  | .phi => 20 | .chi => 21 | .psi => 22 | .omega => 23

-- <vc-helpers>
-- </vc-helpers>

def greek_comparator (a b : GreekLetter) : Int :=
  sorry

theorem greek_comparator_reflexive (a : GreekLetter) : 
  greek_comparator a a = 0 :=
sorry

theorem greek_comparator_antisymmetric (a b : GreekLetter) :
  greek_comparator a b = -(greek_comparator b a) :=
sorry 

theorem greek_comparator_transitive (a b c : GreekLetter) :
  greek_comparator a b > 0 → greek_comparator b c > 0 → greek_comparator a c > 0 :=
sorry

theorem greek_comparator_position {a b : GreekLetter} :
  a = b → greek_comparator a b = 0 :=
sorry

theorem greek_comparator_order {a b : GreekLetter} :
  greek_index a < greek_index b → greek_comparator a b < 0 :=
sorry

theorem greek_comparator_order_reverse {a b : GreekLetter} :
  greek_index a > greek_index b → greek_comparator a b > 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval greek_comparator "chi" "chi"

-- Apps difficulty: introductory
-- Assurance level: guarded