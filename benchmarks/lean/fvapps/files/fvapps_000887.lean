-- <vc-preamble>
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
  | (h::t) => h :: t

def generateRange (n : Nat) : List Int :=
  List.map Int.ofNat (List.range n)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_min_distance (n k : Nat) (x : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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

theorem find_max_min_distance_k2
    {n : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : x.length = n)
    (h3 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h4 : x.Nodup) :
    find_max_min_distance n 2 x ≤ listMax x - listMin x :=
sorry

theorem find_max_min_distance_sort_invariant
    {n : Nat} {x : List Int}
    (h1 : n ≥ 2)
    (h2 : x.length = n)
    (h3 : ∀ i ∈ x, i ≥ 1 ∧ i ≤ 1000)
    (h4 : x.Nodup) :
    find_max_min_distance n 2 x = find_max_min_distance n 2 (listToSorted x) :=
sorry

theorem find_max_min_distance_evenly_spaced
    {n k : Nat}
    (h1 : n ≥ 2)
    (h2 : k ≥ 2)
    (h3 : k ≤ n) :
    find_max_min_distance n k (generateRange n) = (n-1) / (k-1) :=
sorry
-- </vc-theorems>