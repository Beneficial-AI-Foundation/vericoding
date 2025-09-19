-- <vc-preamble>
def Heap := List Int

def ins (l : Heap) (x : Int) : Heap := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pop (l : Heap) : Int × Heap := sorry

/- The heap maintains the min-heap property after insertions -/
-- </vc-definitions>

-- <vc-theorems>
theorem heap_maintains_min_property {h : Heap} (xs : List Int) : 
  let h' := xs.foldl (fun acc x => ins acc x) h
  ∀ i, 2 ≤ i → i < h'.length → 
    match h'.get? i, h'.get? (i/2) with
    | some vi, some vp => vi ≥ vp
    | _, _ => True := sorry
-- </vc-theorems>