import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_452_CalculateLoss",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_452_CalculateLoss",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Calculates the loss amount given cost price and selling price.
If cost price is greater than selling price, returns the difference.
Otherwise returns 0.

@param costPrice The cost price (must be non-negative)
@param sellingPrice The selling price (must be non-negative)
@return The calculated loss amount
-/
def CalculateLoss (costPrice : Int) (sellingPrice : Int) : Int := sorry

/--
Specification for CalculateLoss:
- Requires both prices to be non-negative
- Ensures loss is cost price minus selling price when cost price is higher
- Ensures loss is 0 when cost price is not higher than selling price
-/
theorem CalculateLoss_spec (costPrice : Int) (sellingPrice : Int) :
  costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
  ((costPrice > sellingPrice → CalculateLoss costPrice sellingPrice = costPrice - sellingPrice) ∧
   (costPrice ≤ sellingPrice → CalculateLoss costPrice sellingPrice = 0)) := sorry

end DafnyBenchmarks