

/-!
{
"name": "Clover_convert_map_key_convert_map_key",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_convert_map_key_convert_map_key",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Converts a map by applying a function to its keys while preserving values.
The function must be injective (one-to-one) on the domain.

@param inputs The input map from naturals to booleans
@param f The function to apply to the keys
@return A new map with transformed keys
-/
def convert_map_key (inputs : Nat → Option Bool) (f : Nat → Nat) : Nat → Option Bool := sorry

/--
Specification for convert_map_key ensuring:
1. The mapping function is injective (one-to-one)
2. Keys are preserved under transformation
3. Values are preserved for transformed keys
-/
theorem convert_map_key_spec
(inputs : Nat → Option Bool)
(f : Nat → Nat) :
(∀ n1 n2 : Nat, n1 ≠ n2 → f n1 ≠ f n2) →
(∀ k : Nat, (inputs k).isSome ↔ (convert_map_key inputs f (f k)).isSome) ∧
(∀ k : Nat, (inputs k).isSome → convert_map_key inputs f (f k) = inputs k) := sorry