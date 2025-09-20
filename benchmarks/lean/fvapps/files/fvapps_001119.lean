-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_expected_hearts (n m k: Nat) (hearts: List Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expected_hearts_bounded 
  (n m k: Nat) (hearts: List Nat)
  (h1: n > 0) (h2: m > 0) (h3: k > 0) (h4: hearts.length = k)
  (h5: ∀ h ∈ hearts, 1 ≤ h ∧ h ≤ n*m) :
  let result := calculate_expected_hearts n m k hearts
  0 ≤ result ∧ result ≤ Float.ofNat k :=
sorry

theorem expected_hearts_symmetry
  (n m k: Nat) (hearts: List Nat)
  (h1: n > 0) (h2: m > 0) (h3: k > 0) (h4: hearts.length = k)
  (h5: ∀ h ∈ hearts, 1 ≤ h ∧ h ≤ n*m) :
  let hearts_flipped := hearts.map (fun h => ((h-1)/m)*m + (m - (h-1)%m))
  let result := calculate_expected_hearts n m k hearts
  let result_flipped := calculate_expected_hearts n m k hearts_flipped
  Float.abs (result - result_flipped) < 1e-10 :=
sorry

theorem single_heart_bounded
  (n m: Nat) (pos: Nat)
  (h1: n > 0) (h2: m > 0) (h3: 1 ≤ pos) (h4: pos ≤ n*m) :
  let result := calculate_expected_hearts n m 1 [pos]
  0 ≤ result ∧ result ≤ 1 :=
sorry

theorem corner_hearts_symmetry
  (n m: Nat) 
  (h1: n > 0) (h2: m > 1) :
  let result1 := calculate_expected_hearts n m 1 [1]
  let result2 := calculate_expected_hearts n m 1 [m]
  Float.abs (result1 - result2) < 1e-10 :=
sorry
-- </vc-theorems>