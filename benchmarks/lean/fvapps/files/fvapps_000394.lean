-- <vc-preamble>
def listMin (xs : List Int) : Float :=
  match xs with
  | [] => 0
  | (h::t) => Float.ofInt (List.foldl min h t)

def listMax (xs : List Int) : Float :=
  match xs with
  | [] => 0
  | (h::t) => Float.ofInt (List.foldl max h t)

def listSum (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | (h::t) => h + listSum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_stats (numbers: List Int) : Float × Float × Float × Float :=
  sorry

def sorted (xs : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_stats_empty :
  array_stats [] = (0, 0, 0, 0) :=
sorry

theorem array_stats_mean (numbers: List Int) (h: numbers ≠ []) :
  let (mean, _, _, _) := array_stats numbers
  (mean - Float.ofInt (listSum numbers) / Float.ofInt numbers.length).abs < 1e-10 :=
sorry

theorem array_stats_minmax (numbers: List Int) (h: numbers ≠ []) :
  let (_, _, min_val, max_val) := array_stats numbers
  min_val = listMin numbers ∧
  max_val = listMax numbers :=
sorry

theorem array_stats_ordering (numbers: List Int) (h: numbers ≠ []) :
  let (mean, median, min_val, max_val) := array_stats numbers
  min_val ≤ median ∧ median ≤ max_val ∧
  min_val ≤ mean ∧ mean ≤ max_val :=
sorry

theorem array_stats_median_even (numbers: List Int) (h: numbers ≠ [])
  (h2: numbers.length % 2 = 0) :
  let (_, median, _, _) := array_stats numbers
  let s := sorted numbers
  (median - Float.ofInt ((List.get! s ((numbers.length)/2 - 1)) + (List.get! s (numbers.length/2)))/2).abs < 1e-10 :=
sorry

theorem array_stats_median_odd (numbers: List Int) (h: numbers ≠ [])
  (h2: numbers.length % 2 = 1) :
  let (_, median, _, _) := array_stats numbers
  let s := sorted numbers
  (median - Float.ofInt (List.get! s (numbers.length/2))).abs < 1e-10 :=
sorry
-- </vc-theorems>