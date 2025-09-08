/-
```if:csharp
## Terminal Game - Create Hero Class

In this first kata in the series, you need to define a Hero class to be used in a terminal game. The hero should have the following attributes:

attribute | type | value
---|---|---
Name | string | user argument or "Hero"
Position | string | "00"
Health | float | 100
Damage | float | 5
Experience | int | 0
```

```if-not:csharp
## Terminal Game - Create Hero Prototype

In this first kata in the series, you need to define a Hero prototype to be used in a terminal game. The hero should have the following attributes:

attribute | value
---|---
name | user argument or 'Hero'
position | '00'
health | 100
damage | 5
experience | 0
```
-/

-- <vc-helpers>
-- </vc-helpers>

def Hero.new : Hero := sorry
def Hero.newWithName (name : String) : Hero := sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded