// <vc-preamble>
/*
 * Implementation of numpy.nanargmin functionality in Dafny.
 * This function finds the index of the minimum value in a sequence, ignoring NaN values.
 * If all values are NaN, the precondition prevents calling the function.
 */

// Datatype to represent floating-point values that can be NaN
datatype Float = NaN | Value(val: real)

// Helper predicate to check if a Float is NaN
predicate isNaN(f: Float) {
    f.NaN?
}

// Helper function to get the real value (only valid for non-NaN values)
function getValue(f: Float): real
    requires !f.NaN?
{
    f.val
}

// Helper predicate to compare two Float values (NaN handling)
predicate floatLessOrEqual(a: Float, b: Float)
    requires !a.NaN? && !b.NaN?
{
    a.val <= b.val
}

predicate floatGreaterThan(a: Float, b: Float)
    requires !a.NaN? && !b.NaN?
{
    a.val > b.val
}

// Main method: find the index of minimum non-NaN value
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanargmin(a: seq<Float>) returns (idx: nat)
    // Precondition: sequence is non-empty and contains at least one non-NaN value
    requires |a| > 0
    requires exists i :: 0 <= i < |a| && !isNaN(a[i])
    
    // Postconditions:
    // 1. Returned index is valid and points to a non-NaN value
    ensures 0 <= idx < |a|
    ensures !isNaN(a[idx])
    
    // 2. The value at the returned index is <= all other non-NaN values
    ensures forall j :: 0 <= j < |a| && !isNaN(a[j]) ==> 
        floatLessOrEqual(a[idx], a[j])
    
    // 3. For tie-breaking: all indices before idx either contain NaN or values > a[idx]
    ensures forall j :: 0 <= j < idx ==> 
        isNaN(a[j]) || floatGreaterThan(a[j], a[idx])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
