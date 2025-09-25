-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (h::t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_monster_invaders (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_monster_invaders_nonnegative (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 10)
  (h5 : r2 > 0) (h6 : r2 ≤ 10)
  (h7 : r3 > 0) (h8 : r3 ≤ 10)
  (h9 : d > 0) (h10 : d ≤ 10)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n r1 r2 r3 d monsters ≥ 0 :=
  sorry

theorem solve_monster_invaders_upper_bound (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 10)
  (h5 : r2 > 0) (h6 : r2 ≤ 10)
  (h7 : r3 > 0) (h8 : r3 ≤ 10)
  (h9 : d > 0) (h10 : d ≤ 10)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n r1 r2 r3 d monsters ≤ (n-1)*d + (List.map (λ m => (m+2)*r1) monsters).sum + n*(r2+r3) :=
  sorry

theorem solve_monster_invaders_monotone_r1 (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 9)
  (h5 : r2 > 0) (h6 : r2 ≤ 10)
  (h7 : r3 > 0) (h8 : r3 ≤ 10)
  (h9 : d > 0) (h10 : d ≤ 10)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n (r1+1) r2 r3 d monsters ≥ solve_monster_invaders n r1 r2 r3 d monsters :=
  sorry

theorem solve_monster_invaders_monotone_r2 (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 10)
  (h5 : r2 > 0) (h6 : r2 ≤ 9)
  (h7 : r3 > 0) (h8 : r3 ≤ 10)
  (h9 : d > 0) (h10 : d ≤ 10)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n r1 (r2+1) r3 d monsters ≥ solve_monster_invaders n r1 r2 r3 d monsters :=
  sorry

theorem solve_monster_invaders_monotone_r3 (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 10)
  (h5 : r2 > 0) (h6 : r2 ≤ 10)
  (h7 : r3 > 0) (h8 : r3 ≤ 9)
  (h9 : d > 0) (h10 : d ≤ 10)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n r1 r2 (r3+1) d monsters ≥ solve_monster_invaders n r1 r2 r3 d monsters :=
  sorry

theorem solve_monster_invaders_monotone_d (n : Nat) (r1 r2 r3 d : Nat) (monsters : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : r1 > 0) (h4 : r1 ≤ 10)
  (h5 : r2 > 0) (h6 : r2 ≤ 10)
  (h7 : r3 > 0) (h8 : r3 ≤ 10)
  (h9 : d > 0) (h10 : d ≤ 9)
  (h11 : monsters.length = n)
  (h12 : ∀ m ∈ monsters, m ≥ 0 ∧ m ≤ 10) :
  solve_monster_invaders n r1 r2 r3 (d+1) monsters ≥ solve_monster_invaders n r1 r2 r3 d monsters :=
  sorry

/-
info: 34
-/
-- #guard_msgs in
-- #eval solve_monster_invaders 4 1 3 4 3 [3, 2, 5, 1]

/-
info: 31
-/
-- #guard_msgs in
-- #eval solve_monster_invaders 4 2 4 4 1 [4, 5, 1, 2]

/-
info: 23
-/
-- #guard_msgs in
-- #eval solve_monster_invaders 2 2 5 7 3 [4, 5]
-- </vc-theorems>