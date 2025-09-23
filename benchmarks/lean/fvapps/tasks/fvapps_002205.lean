-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_fatigue (n a b : Nat) (x : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_fatigue_non_negative 
  {n a b : Nat} 
  {x : List Nat}
  (h1 : a > 0) 
  (h2 : b > 0)
  (h3 : x.length = n)
  (h4 : ∀ (i j : Fin x.length), i.val < j.val → x.get i < x.get j) :
  min_fatigue n a b x ≥ 0 :=
sorry

theorem min_fatigue_teleport_bound
  {n a b : Nat}
  {x : List Nat}
  (h1 : a > 0)
  (h2 : b > 0) 
  (h3 : x.length = n)
  (h4 : ∀ (i j : Fin x.length), i.val < j.val → x.get i < x.get j) :
  min_fatigue n a b x ≤ b * (n - 1) :=
sorry

theorem min_fatigue_walk_bound
  {n a b : Nat}
  {x : List Nat}
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : x.length = n)
  (h4 : ∀ (i j : Fin x.length), i.val < j.val → x.get i < x.get j)
  (h5 : n > 0) :
  min_fatigue n a b x ≤ a * (x.get ⟨n-1, sorry⟩ - x.get ⟨0, sorry⟩) :=
sorry

theorem min_fatigue_scale_invariant
  {n a b s : Nat}
  {x : List Nat}
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : s > 0)
  (h4 : x.length = n)
  (h5 : ∀ (i j : Fin x.length), i.val < j.val → x.get i < x.get j) :
  min_fatigue n (a * s) (b * s) x = s * min_fatigue n a b x :=
sorry
-- </vc-theorems>