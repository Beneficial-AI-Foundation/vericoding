import Mathlib
-- <vc-preamble>
structure Wave where
  start_time : Nat
  end_time : Nat
  monsters : Nat
deriving Inhabited, DecidableEq

def ValidWaves (waves : List Wave) : Prop :=
  ∀ i, i < waves.length → 
    waves[i]!.start_time ≤ waves[i]!.end_time ∧
    waves[i]!.monsters > 0 ∧
    (i > 0 → waves[i-1]!.end_time ≤ waves[i]!.start_time)

def CalculateReloadsNeeded (monsters : Nat) (k : Nat) : Nat :=
  if k > 0 then
    if monsters ≤ k then 0
    else (monsters - 1) / k
  else 0

def CanReachWaveInTime (waves : List Wave) (waveIndex : Nat) (k : Nat) : Prop :=
  if waveIndex > 0 ∧ waveIndex < waves.length ∧ k > 0 then
    let prevWave := waves[waveIndex - 1]!
    let currWave := waves[waveIndex]!
    let timeGap := currWave.start_time - prevWave.end_time
    let reloadsNeeded := CalculateReloadsNeeded prevWave.monsters k
    reloadsNeeded ≤ timeGap
  else True

def CanSolveWave (waves : List Wave) (waveIndex : Nat) (k : Nat) : Prop :=
  if waveIndex < waves.length ∧ k > 0 then
    let wave := waves[waveIndex]!
    let timeAvailable := wave.end_time - wave.start_time + 1
    let maxPossibleShots := timeAvailable * k
    wave.monsters ≤ maxPossibleShots ∧
    (waveIndex = 0 ∨ CanReachWaveInTime waves waveIndex k)
  else False

def CanSolveAllWaves (waves : List Wave) (k : Nat) : Prop :=
  k > 0 ∧ 
  ∀ i, i < waves.length → CanSolveWave waves i k

def CalculateMinimumBulletsHelper (waves : List Wave) (k : Nat) (index : Nat) (currentAmmo : Nat) : Nat :=
  if index < waves.length then
    let wave := waves[index]!
    let bulletsNeeded := wave.monsters
    let totalBullets := if currentAmmo ≥ bulletsNeeded then 0 else bulletsNeeded
    totalBullets + CalculateMinimumBulletsHelper waves k (index + 1) k
  else 0

def CalculateMinimumBullets (waves : List Wave) (k : Nat) : Nat :=
  CalculateMinimumBulletsHelper waves k 0 k

@[reducible, simp]
def solve_precond (waves : List Wave) (k : Nat) : Prop :=
  ValidWaves waves ∧ k > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance CanReachWaveInTime.decidable (waves : List Wave) (waveIndex : Nat) (k : Nat) : Decidable (CanReachWaveInTime waves waveIndex k) := by
  unfold CanReachWaveInTime; infer_instance

-- LLM HELPER
instance CanSolveWave.decidable (waves : List Wave) (waveIndex : Nat) (k : Nat) : Decidable (CanSolveWave waves waveIndex k) := by
  unfold CanSolveWave; infer_instance

-- LLM HELPER
instance CanSolveAllWaves.decidable (waves : List Wave) (k : Nat) : Decidable (CanSolveAllWaves waves k) := by
  unfold CanSolveAllWaves; infer_instance

-- LLM HELPER
lemma natCast_ne_neg_one (n : Nat) : (n : Int) ≠ -1 := by
  intro h
  have : (n : Int) ≥ 0 := Int.natCast_nonneg n
  rw [h] at this
  linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (waves : List Wave) (k : Nat) (h_precond : solve_precond waves k) : Int :=
  if CanSolveAllWaves waves k then
    Int.ofNat (CalculateMinimumBullets waves k)
  else
    -1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (waves : List Wave) (k : Nat) (result : Int) (h_precond : solve_precond waves k) : Prop :=
  (result = -1 ↔ ¬CanSolveAllWaves waves k) ∧
  (result ≥ 0 ↔ CanSolveAllWaves waves k) ∧
  (CanSolveAllWaves waves k → result = CalculateMinimumBullets waves k)

theorem solve_spec_satisfied (waves : List Wave) (k : Nat) (h_precond : solve_precond waves k) :
    solve_postcond waves k (solve waves k h_precond) h_precond := by
  unfold solve
  split_ifs with h_cansolve
  · -- case CanSolveAllWaves waves k
    simp [solve_postcond, h_cansolve, Int.natCast_nonneg, natCast_ne_neg_one]
  · -- case ¬CanSolveAllWaves waves k
    simp [solve_postcond, h_cansolve]
-- </vc-theorems>
