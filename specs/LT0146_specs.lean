-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Time unit codes for timedelta64 -/
inductive TimeUnit where
  /-- Year unit ('Y') -/
  | year       
  /-- Month unit ('M') -/
  | month      
  /-- Week unit ('W') -/
  | week       
  /-- Day unit ('D') -/
  | day        
  /-- Hour unit ('h') -/
  | hour       
  /-- Minute unit ('m') -/
  | minute     
  /-- Second unit ('s') -/
  | second     
  /-- Millisecond unit ('ms') -/
  | millisecond 
  /-- Microsecond unit ('us') -/
  | microsecond 
  /-- Nanosecond unit ('ns') -/
  | nanosecond 
  /-- Picosecond unit ('ps') -/
  | picosecond 
  /-- Femtosecond unit ('fs') -/
  | femtosecond 
  /-- Attosecond unit ('as') -/
  | attosecond

/-- Represents a time duration value -/
structure TimeDelta64 where
  /-- The numeric value of the time duration -/
  value : Int64
  /-- The time unit for the duration -/
  unit : TimeUnit
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def timedelta64 (value : Int64) (unit : TimeUnit) : Id TimeDelta64 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem timedelta64_spec (value : Int64) (unit : TimeUnit) :
    ⦃⌜True⌝⦄
    timedelta64 value unit
    ⦃⇓result => ⌜result.value = value ∧ result.unit = unit ∧ 
                result.value ≥ -9223372036854775808 ∧ 
                result.value ≤ 9223372036854775807⌝⦄ := by
  sorry
-- </vc-theorems>