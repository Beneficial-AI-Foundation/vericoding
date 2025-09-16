-- <vc-preamble>
structure Wave where
  start_time : Nat
  end_time : Nat
  monsters : Nat
deriving Inhabited

def ValidWaves (waves : List Wave) : Prop :=
  ∀ i, i < waves.length → 
    waves[i]!.start_time ≤ waves[i]!.end_time ∧
    waves[i]!.monsters > 0 ∧
    (i > 0 → waves[i-1]!.end_time ≤ waves[i]!.start_time)

def CalculateReloadsNeeded (monsters k : Nat) : Nat :=
  if monsters ≤ k then 0
  else (monsters - 1) / k

def CanReachWaveInTime (waves : List Wave) (waveIndex k : Nat) : Prop :=
  waveIndex > 0 ∧ waveIndex < waves.length ∧ k > 0 →
  let prevWave := waves[waveIndex - 1]!
  let currWave := waves[waveIndex]!
  let timeGap := currWave.start_time - prevWave.end_time
  let reloadsNeeded := CalculateReloadsNeeded prevWave.monsters k
  reloadsNeeded ≤ timeGap

def CanSolveWave (waves : List Wave) (waveIndex k : Nat) : Prop :=
  waveIndex < waves.length ∧ k > 0 →
  let wave := waves[waveIndex]!
  let timeAvailable := wave.end_time - wave.start_time + 1
  let maxPossibleShots := timeAvailable * k
  wave.monsters ≤ maxPossibleShots ∧
  (waveIndex = 0 ∨ CanReachWaveInTime waves waveIndex k)

def CanSolveAllWaves (waves : List Wave) (k : Nat) : Prop :=
  k > 0 ∧ 
  ∀ i, i < waves.length → CanSolveWave waves i k

def CalculateMinimumBulletsHelper (waves : List Wave) (k bulletCount remainingBullets : Nat) : Nat :=
  sorry

def CalculateMinimumBullets (waves : List Wave) (k : Nat) : Nat :=
  CalculateMinimumBulletsHelper waves k 0 k

@[reducible, simp]
def solve_precond (waves : List Wave) (k : Nat) : Prop :=
  ValidWaves waves ∧ k > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (waves : List Wave) (k : Nat) (h_precond : solve_precond waves k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (waves : List Wave) (k : Nat) (result : Int) (h_precond : solve_precond waves k) : Prop :=
  (result = -1 ↔ ¬CanSolveAllWaves waves k) ∧
  (result ≥ 0 ↔ CanSolveAllWaves waves k) ∧
  (CanSolveAllWaves waves k → result = CalculateMinimumBullets waves k)

theorem solve_spec_satisfied (waves : List Wave) (k : Nat) (h_precond : solve_precond waves k) :
    solve_postcond waves k (solve waves k h_precond) h_precond := by
  sorry
-- </vc-theorems>
