-- <vc-preamble>
def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl Nat.max x xs

def listToFinset (l : List Nat) : List Nat :=
  l.eraseDups
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def windowsOfSize (l : List Nat) (size : Nat) : List (List Nat) :=
  sorry

def min_subscriptions (n k d : Nat) (shows : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_subscriptions_output_bounds
  (shows : List Nat)
  (h1 : shows ≠ [])
  (h2 : ∀ x ∈ shows, 1 ≤ x ∧ x ≤ 100) :
  let n := shows.length
  let k := maximum shows
  let d := min n (maximum shows)
  let result := min_subscriptions n k d shows
  1 ≤ result ∧ result ≤ (listToFinset shows).length :=
sorry

theorem min_subscriptions_window_size_one
  (shows : List Nat)
  (h1 : shows ≠ [])
  (h2 : ∀ x ∈ shows, 1 ≤ x) :
  let n := shows.length
  let k := maximum shows
  min_subscriptions n k 1 shows = 1 :=
sorry

theorem min_subscriptions_window_size_equals_length
  (shows : List Nat)
  (k : Nat)
  (h1 : shows ≠ [])
  (h2 : ∀ x ∈ shows, 1 ≤ x)
  (h3 : 1 ≤ k) :
  let n := shows.length
  min_subscriptions n k n shows = (listToFinset shows).length :=
sorry

theorem min_subscriptions_repeated_elements
  (shows : List Nat)
  (h1 : shows ≠ [])
  (h2 : ∀ x ∈ shows, 1 ≤ x) :
  let n := shows.length
  let k := maximum shows
  let d := n
  min_subscriptions n k d shows = min_subscriptions (2*n) k d (shows ++ shows) :=
sorry

theorem min_subscriptions_sliding_window
  (shows : List Nat)
  (window_size : Nat)
  (h1 : shows.length ≥ 2)
  (h2 : window_size ≥ 2)
  (h3 : ∀ x ∈ shows, 1 ≤ x) :
  let n := shows.length
  let k := maximum shows
  let d := min window_size n
  let result := min_subscriptions n k d shows
  let windows := windowsOfSize shows d
  let min_unique := (windows.map (fun w => (listToFinset w).length)).foldl Nat.min n
  result = min_unique :=
sorry
-- </vc-theorems>