-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Dog.bark (d : Dog) : String := sorry

theorem dog_breed_property {breed : String} :
  (Dog.mk breed).breed = breed := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dog_bark_property (d : Dog) :
  d.bark = "Woof" := sorry

theorem dog_state_independence {breed1 breed2 : String} (h : breed1 ≠ breed2) :
  let d1 := Dog.mk breed1
  let d2 := Dog.mk breed2
  d1.breed ≠ d2.breed ∧ d1.bark = d2.bark := sorry
-- </vc-theorems>