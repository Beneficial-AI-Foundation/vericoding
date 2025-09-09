def find_max_min_distance (n k : Nat) (x : List Int) : Nat :=
  sorry

-- Helper functions for max/min

def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | (h::t) => List.foldl max h t

def listMin (xs : List Int) : Int :=
  match xs with
  | [] => 0  
  | (h::t) => List.foldl min h t

def listToSorted (xs : List Int) : List Int :=
  match xs with
  | [] => []
  | (h::t) => h :: t -- simplified for theorem statement

-- Non-negative result

-- <vc-helpers>
-- </vc-helpers>

def generateRange (n : Nat) : List Int :=
  List.map Int.ofNat (List.range n)

-- Evenly spaced points

theorem find_max_min_distance_nonneg
    {n k : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : k ≥ 2) 
    (h3 : k ≤ n)
    (h4 : x.length = n)
    (h5 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h6 : x.Nodup) :
    find_max_min_distance n k x ≥ 0 :=
  sorry

-- Result bounded by max distance

theorem find_max_min_distance_bounded
    {n k : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : k ≥ 2)
    (h3 : k ≤ n)
    (h4 : x.length = n)
    (h5 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h6 : x.Nodup) :
    find_max_min_distance n k x ≤ listMax x - listMin x :=
  sorry

-- Special case for k=2

theorem find_max_min_distance_k2
    {n : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : x.length = n)
    (h3 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h4 : x.Nodup) :
    find_max_min_distance n 2 x ≤ listMax x - listMin x :=
  sorry

-- Sorting invariance

theorem find_max_min_distance_sort_invariant
    {n : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : x.length = n)
    (h3 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h4 : x.Nodup) :
    find_max_min_distance n 2 x = find_max_min_distance n 2 (listToSorted x) :=
  sorry

-- Evenly spaced integers

theorem find_max_min_distance_evenly_spaced
    {n k : Nat}
    (h1 : n ≥ 2)
    (h2 : k ≥ 2)
    (h3 : k ≤ n) :
    find_max_min_distance n k (generateRange n) = (n-1) / (k-1) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_min_distance 2 2 [1, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_min_distance 5 3 [1, 2, 8, 4, 9]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_min_distance 4 2 [1, 2, 3, 4]

-- Apps difficulty: interview
-- Assurance level: guarded