-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zombieShootout (zombies ammo : Int) (distance : Float) : String := sorry 

def containsStr (s₁ s₂ : String) : Bool := 
  let s₁chars := s₁.data
  let s₂chars := s₂.data
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>