-- <vc-preamble>
def DateTime := Nat -- simplified representation
def TimeDelta := Nat -- simplified representation

instance : Add DateTime where
  add := Nat.add

instance : HAdd DateTime TimeDelta DateTime where
  hAdd := Nat.add
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elapsedSeconds (s e : DateTime) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem elapsedSeconds_nonnegative
  (s : DateTime)
  (e : DateTime)
  (d : TimeDelta)
  (h : e = s + d) :
  elapsedSeconds s e ≥ 0 :=
  sorry

theorem elapsedSeconds_matches_delta
  (s : DateTime)
  (e : DateTime) 
  (d : TimeDelta)
  (h : e = s + d) :
  elapsedSeconds s e = d :=
  sorry

theorem elapsedSeconds_identity
  (dt : DateTime) :
  elapsedSeconds dt dt = 0 :=
  sorry

/-
info: 3600
-/
-- #guard_msgs in
-- #eval elapsed_seconds datetime(2020, 1, 1, 0, 0, 0) datetime(2020, 1, 1, 1, 0, 0)

/-
info: 60
-/
-- #guard_msgs in
-- #eval elapsed_seconds datetime(2020, 1, 1, 0, 0, 0) datetime(2020, 1, 1, 0, 1, 0)

/-
info: 1
-/
-- #guard_msgs in
-- #eval elapsed_seconds datetime(2020, 1, 1, 0, 0, 0) datetime(2020, 1, 1, 0, 0, 1)
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded