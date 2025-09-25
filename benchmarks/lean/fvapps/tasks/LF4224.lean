-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def megaMind (hp dps shots regen : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem megaMind_positive {hp dps shots regen : Nat} (h1 : hp > 0) (h2 : dps > 0) 
  (h3 : shots > 0) : 
  megaMind hp dps shots regen = -1 ∨ megaMind hp dps shots regen > 0 := 
  sorry

theorem megaMind_impossible_case {hp dps shots regen : Nat} (h1 : hp > 0) (h2 : dps > 0)
  (h3 : shots > 0) :
  megaMind hp dps shots regen = -1 ↔ dps * shots ≤ regen := 
  sorry

theorem megaMind_minimum_turns {hp dps shots regen : Nat} (h1 : hp > 0) (h2 : dps > 0)
  (h3 : shots > 0) :
  megaMind hp dps shots regen ≠ -1 → 
  megaMind hp dps shots regen ≥ (hp + dps - 1) / dps := 
  sorry

theorem megaMind_bounds {hp dps shots regen : Nat} :
  hp ≤ 10000 →
  dps ≤ 1000 →
  shots ≤ 100 →
  regen ≤ 1000 →
  True :=
  sorry
-- </vc-theorems>