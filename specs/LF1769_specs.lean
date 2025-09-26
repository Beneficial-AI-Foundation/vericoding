-- <vc-preamble>
def AllOne.inc (a : AllOne) (key : String) : Unit := sorry
def AllOne.dec (a : AllOne) (key : String) : Unit := sorry

def AllOne.getMaxKey (a : AllOne) : String := sorry
def AllOne.getMinKey (a : AllOne) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countMap (keys : List String) : String → Nat
  | s => List.length (List.filter (· = s) keys)
-- </vc-definitions>

-- <vc-theorems>
theorem increment_maintains_order (keys : List String) (a : AllOne) (h : keys ≠ []) :
  (∀ k ∈ keys, 
    let counts := countMap keys
    let maxCount := List.foldl (fun acc k => max acc (counts k)) 0 keys
    let maxKeys := List.filter (fun k => counts k = maxCount) keys
    let minCount := List.foldl (fun acc k => min acc (counts k)) (maxCount + 1) keys
    let minKeys := List.filter (fun k => counts k = minCount) keys
    a.getMaxKey ∈ maxKeys ∧ a.getMinKey ∈ minKeys) := sorry

theorem empty_after_decrement (keys : List String) (a : AllOne) (h : keys ≠ []) :
  a.getMaxKey = "" ∧ a.getMinKey = "" := sorry
-- </vc-theorems>