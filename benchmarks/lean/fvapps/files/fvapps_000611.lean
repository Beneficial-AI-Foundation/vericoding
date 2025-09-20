-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_magic_potions (R G B M : Nat) (r g b : List Nat) : Nat := sorry

def list_max (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs
-- </vc-definitions>

-- <vc-theorems>
theorem magic_potions_result_non_negative 
  (R G B M : Nat)
  (r g b : List Nat)
  (hR : R > 0)
  (hG : G > 0) 
  (hB : B > 0)
  (hr : r.length = R)
  (hg : g.length = G)
  (hb : b.length = B)
  (h_non_empty : ∀ x ∈ r ++ g ++ b, x > 0) :
  solve_magic_potions R G B M r g b ≥ 0 := sorry

theorem magic_potions_result_bounded
  (R G B M : Nat)
  (r g b : List Nat)
  (hR : R > 0)
  (hG : G > 0)
  (hB : B > 0)
  (hr : r.length = R)
  (hg : g.length = G) 
  (hb : b.length = B)
  (h_non_empty : ∀ x ∈ r ++ g ++ b, x > 0) :
  solve_magic_potions R G B M r g b ≤ max (max (list_max r) (list_max g)) (list_max b) := sorry

theorem magic_potions_zero_operations
  (R G B : Nat)
  (r g b : List Nat) 
  (hR : R > 0)
  (hG : G > 0)
  (hB : B > 0)
  (hr : r.length = R)
  (hg : g.length = G)
  (hb : b.length = B)
  (h_non_empty : ∀ x ∈ r ++ g ++ b, x > 0) :
  solve_magic_potions R G B 0 r g b = max (max (list_max r) (list_max g)) (list_max b) := sorry

theorem magic_potions_single_elements
  (M : Nat)
  (r g b : List Nat)
  (hr : r.length = 1)
  (hg : g.length = 1)
  (hb : b.length = 1)
  (h_non_empty : ∀ x ∈ r ++ g ++ b, x > 0) :
  let max_val := max (max (list_max r) (list_max g)) (list_max b)
  solve_magic_potions 1 1 1 M r g b ≤ max_val ∧ 
  solve_magic_potions 1 1 1 M r g b ≥ max_val / (2^M) := sorry
-- </vc-theorems>