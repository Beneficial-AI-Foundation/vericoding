-- <vc-preamble>
def contains (xs : List Int) (x : Int) : Bool :=
  xs.foldl (fun acc y => acc || y == x) false

def countLessThan (xs : List Int) (x : Int) : Nat :=
  xs.foldl (fun acc y => if y < x then acc + 1 else acc) 0

def uniqueList (xs : List Int) : List Int :=
  xs.foldl (fun acc x => if contains acc x then acc else x::acc) []

def minimum (xs : List Int) : Option Int :=
  xs.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (min x m)) none

def maximum (xs : List Int) : Option Int :=
  xs.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (max x m)) none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_smallest (arr : List Int) (n : Nat) : Option Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nth_smallest_properties {arr : List Int} {n : Nat} (h : n ≥ 1) :
  match nth_smallest arr n with
  | none => n > (uniqueList arr).length
  | some result =>
    (n ≤ (uniqueList arr).length) ∧
    contains arr result ∧
    countLessThan (uniqueList arr) result = n-1
  :=
sorry

theorem nth_smallest_first {arr : List Int} (h : arr ≠ []) :
  nth_smallest arr 1 = minimum (uniqueList arr) :=
sorry

theorem nth_smallest_last_valid {arr : List Int} (h : arr ≠ []) :
  nth_smallest arr (uniqueList arr).length = maximum (uniqueList arr) :=
sorry

theorem nth_smallest_empty :
  nth_smallest [] 1 = none :=
sorry
-- </vc-theorems>