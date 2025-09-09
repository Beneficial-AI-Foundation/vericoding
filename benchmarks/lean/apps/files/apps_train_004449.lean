-- <vc-helpers>
-- </vc-helpers>

def bar_triang (a b c : Prod Float Float) : Prod Float Float :=
  sorry

theorem centroid_is_mean (a b c : Prod Float Float) :
  bar_triang a b c = (((a.1 + b.1 + c.1) / 3), ((a.2 + b.2 + c.2) / 3)) :=
sorry

theorem centroid_order_invariant (a b c : Prod Float Float) :
  bar_triang a b c = bar_triang b c a ∧ 
  bar_triang a b c = bar_triang c a b :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded