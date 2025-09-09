-- <vc-helpers>
-- </vc-helpers>

def min_fatigue (n a b : Nat) (x : List Nat) : Nat :=
  sorry

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

/-
info: 11
-/
-- #guard_msgs in
-- #eval min_fatigue 4 2 5 [1, 2, 5, 7]

/-
info: 84
-/
-- #guard_msgs in
-- #eval min_fatigue 7 1 100 [40, 43, 45, 105, 108, 115, 124]

/-
info: 12
-/
-- #guard_msgs in
-- #eval min_fatigue 7 1 2 [24, 35, 40, 68, 72, 99, 103]

-- Apps difficulty: competition
-- Assurance level: guarded