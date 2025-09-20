-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def looper (start : Float) (stop : Float) (number : Nat) : List Float := sorry

theorem looper_length {start stop : Float} {number : Nat} (h : number > 0) : 
  (looper start stop number).length = number := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem looper_start {start stop : Float} {number : Nat} (h : number > 0) :
  (looper start stop number).head! = start := sorry

theorem looper_stop {start stop : Float} {number : Nat} (h : number > 1) :
  (looper start stop number).getLast! = stop := sorry

theorem looper_evenly_spaced {start stop : Float} {number : Nat} (h : number > 2) :
  let step := (stop - start) / Float.ofNat (number - 1)
  let result := looper start stop number
  ∀ i : Nat, i < result.length - 1 →
    result[i+1]! - result[i]! = step := sorry

theorem looper_single_point {start stop : Float} :
  looper start stop 1 = [start] := sorry
-- </vc-theorems>