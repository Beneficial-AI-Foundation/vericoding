/-
I'm afraid you're in a rather unfortunate situation. You've injured your leg, and are unable to walk, and a number of zombies are shuffling towards you, intent on eating your brains. Luckily, you're a crack shot, and have your trusty rifle to hand.

The zombies start at `range` metres, and move at 0.5 metres per second. Each second, you first shoot one zombie, and then the remaining zombies shamble forwards another 0.5 metres.

If any zombies manage to get to 0 metres, you get eaten. If you run out of ammo before shooting all the zombies, you'll also get eaten. To keep things simple, we can ignore any time spent reloading.

Write a function that accepts the total number of zombies, a range in metres, and the number of bullets you have.

If you shoot all the zombies, return "You shot all X zombies."
If you get eaten before killing all the zombies, and before running out of ammo, return "You shot X zombies before being eaten: overwhelmed."
If you run out of ammo before shooting all the zombies, return "You shot X zombies before being eaten: ran out of ammo."

(If you run out of ammo at the same time as the remaining zombies reach you, return "You shot X zombies before being eaten: overwhelmed.".)

Good luck! (I think you're going to need it.)
-/

-- <vc-helpers>
-- </vc-helpers>

def zombieShootout (zombies ammo : Int) (distance : Float) : String := sorry 

def containsStr (s₁ s₂ : String) : Bool := 
  let s₁chars := s₁.data
  let s₂chars := s₂.data
  sorry

theorem zombieShootout_output_contains_zombies (zombies ammo : Int) (distance : Float)
  (h1 : zombies ≥ 0) (h2 : distance ≥ 0) (h3 : ammo ≥ 0) : 
  containsStr (zombieShootout zombies ammo distance).toLower "zombies" = true := sorry

theorem zombieShootout_zero_zombies (ammo : Int) (distance : Float) 
  (h1 : distance ≥ 0) (h2 : ammo ≥ 0) :
  zombieShootout 0 ammo distance = "You shot all 0 zombies." := sorry

theorem zombieShootout_zero_distance (zombies ammo : Int) (distance : Float)
  (h1 : zombies ≥ 0) (h2 : distance ≤ 0) (h3 : ammo ≥ 0) :
  (zombieShootout zombies ammo distance).endsWith "overwhelmed." := sorry

theorem zombieShootout_zero_ammo (zombies : Int) (distance : Float)
  (h1 : zombies ≥ 0) (h2 : distance ≥ 0) :
  (zombieShootout zombies 0 distance).endsWith "ran out of ammo." := sorry

theorem zombieShootout_all_shot (zombies ammo : Int) (distance : Float)
  (h1 : zombies ≥ 0) (h2 : distance ≥ Float.ofInt zombies / 2) 
  (h3 : ammo ≥ zombies) (h4 : distance ≥ 0) (h5 : ammo ≥ 0) :
  containsStr (zombieShootout zombies ammo distance) "all" → 
  zombieShootout zombies ammo distance = s!"You shot all {zombies} zombies." := sorry

theorem zombieShootout_ran_out_ammo (zombies ammo : Int) (distance : Float)
  (h1 : zombies ≥ 0) (h2 : distance ≥ 0) (h3 : ammo ≥ 0)
  (h4 : zombies > ammo) (h5 : distance > Float.ofInt ammo / 2) :
  (zombieShootout zombies ammo distance).endsWith "ran out of ammo." ∧
  containsStr (zombieShootout zombies ammo distance) (toString ammo) := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded