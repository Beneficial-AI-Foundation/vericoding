-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def happy_g (s : String) : Bool := sorry

theorem happy_g_empty_or_no_g (s : String) :
  ¬ s.contains 'g' → happy_g s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happy_g_multiple_grouped (s : String) :
  (∀ i j : String.Pos, 
    s.get i = 'g' → s.get j = 'g' →
    i.1 + 1 = j.1 → ∃ k : String.Pos, k.1 > j.1 ∧ s.get k = 'g') →
  happy_g s := sorry

theorem happy_g_single_g_unhappy (s : String) (pos : Nat) :
  ¬ s.contains 'g' →
  pos ≤ s.length →
  ¬ happy_g (s.push 'g') := sorry
-- </vc-theorems>