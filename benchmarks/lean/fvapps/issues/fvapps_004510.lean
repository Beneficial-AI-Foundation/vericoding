-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Hero.new : Hero := sorry
def Hero.newWithName (name : String) : Hero := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hero_named_properties (name : String) : 
  let hero := Hero.newWithName name
  hero.name = name ∧ 
  hero.position = "00" ∧ 
  hero.health = 100 ∧ 
  hero.damage = 5 ∧ 
  hero.experience = 0 := sorry

theorem hero_default_properties : 
  let hero := Hero.new
  hero.name = "Hero" ∧ 
  hero.position = "00" ∧ 
  hero.health = 100 ∧ 
  hero.damage = 5 ∧ 
  hero.experience = 0 := sorry
-- </vc-theorems>