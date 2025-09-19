// <vc-preamble>
/*
 * NumPy ufunc ntypes functionality - returns the number of supported 
 * input/output type combinations for a universal function.
 */

// Method to get the number of supported type combinations for a ufunc
// Takes a sequence of strings representing the supported type combinations
// and returns the count of those combinations
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ntypes(ufuncTypeCombinations: seq<string>) returns (result: nat)
    // Precondition: Input must represent valid type combinations for a ufunc
    // A valid ufunc must have at least one supported type combination
    requires |ufuncTypeCombinations| > 0
    // Postcondition: Result equals the exact count of type combinations
    // which is the length of the input sequence and must be positive
    ensures result == |ufuncTypeCombinations|
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
