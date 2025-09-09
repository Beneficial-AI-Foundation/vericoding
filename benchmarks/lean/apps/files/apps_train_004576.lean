/-
The accounts of the "Fat to Fit Club (FFC)" association are supervised by John as a volunteered accountant.
The association is funded through financial donations from generous benefactors. John has a list of
the first `n` donations: `[14, 30, 5, 7, 9, 11, 15]`
He wants to know how much the next benefactor should give to the association so that the 
average of the first `n + 1` donations should reach an average of `30`.
After doing the math he found `149`. He thinks that he made a mistake.
Could you help him?

if `dons = [14, 30, 5, 7, 9, 11, 15]` then `new_avg(dons, 30) --> 149`

The function `new_avg(arr, navg)` should return the expected donation
(rounded up to the next integer) that will permit to reach the average `navg`. 

Should the last donation be a non positive number `(<= 0)` John wants us to throw (or raise) an error or

- return Nothing in Haskell
- return None in F#, Ocaml, Scala
- return `-1` in C, Fortran,  Nim, PowerShell, Go, Prolog
- echo `ERROR` in Shell
- raise-argument-error in Racket

so that he clearly sees that his expectations are not great enough.

Notes: 

- all donations and `navg` are numbers (integers or floats), `arr` can be empty.
- See examples below and "Test Samples" to see which return is to be done.

```
new_avg([14, 30, 5, 7, 9, 11, 15], 92) should return 645
new_avg([14, 30, 5, 7, 9, 11, 15], 2) 
should raise an error (ValueError or invalid_argument or argument-error or DomainError) 
or return `-1` or ERROR or Nothing or None depending on the language.
```
-/

def new_avg (donations : List Int) (targetAvg : Int) : Option Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Int) : Int :=
  sorry

theorem new_avg_type_and_positive (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  ∀ r : Int, new_avg donations targetAvg = some r →
  r > 0 := sorry

theorem new_avg_achieves_target (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  ∀ r : Int, new_avg donations targetAvg = some r →
  ((list_sum donations + r) / (donations.length + 1) - targetAvg).natAbs < 1 := sorry 

theorem new_avg_none_when_negative (donations : List Int) (targetAvg : Int) :
  donations ≠ [] →
  (donations.length + 1) * targetAvg - list_sum donations ≤ 0 →
  new_avg donations targetAvg = none := sorry

theorem new_avg_positive_large_target (donations : List Int) (maxDonation : Int) :
  donations ≠ [] →
  (∀ d ∈ donations, d ≥ 0 ∧ d ≤ maxDonation) →
  let targetAvg := maxDonation + 100
  ∀ r : Int, new_avg donations targetAvg = some r →
  r > 0 := sorry

/-
info: 149
-/
-- #guard_msgs in
-- #eval new_avg [14, 30, 5, 7, 9, 11, 15] 30

/-
info: 645
-/
-- #guard_msgs in
-- #eval new_avg [14, 30, 5, 7, 9, 11, 15] 92

-- Apps difficulty: introductory
-- Assurance level: unguarded