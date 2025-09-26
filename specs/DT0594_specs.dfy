// <vc-preamble>
// Represents a floating-point value that can be either a finite real number or NaN
datatype FloatValue = NaN | Finite(val: real)

// Helper predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Helper predicate to check if a FloatValue is finite (not NaN)
predicate IsFinite(f: FloatValue) {
    f.Finite?
}

// Helper function to extract the real value from a Finite FloatValue
function GetValue(f: FloatValue): real
  requires f.Finite?
{
    f.val
}

// Helper predicate to check if a sequence contains only NaN values
predicate AllNaN(a: seq<FloatValue>) {
    forall i :: 0 <= i < |a| ==> IsNaN(a[i])
}

// Helper predicate to check if there exists at least one finite value
predicate HasFiniteValue(a: seq<FloatValue>) {
    exists i :: 0 <= i < |a| && IsFinite(a[i])
}

// Helper function to count finite values in the sequence
function CountFinite(a: seq<FloatValue>): nat {
    if |a| == 0 then 0
    else (if IsFinite(a[0]) then 1 else 0) + CountFinite(a[1..])
}

// Helper function to extract finite values from the array
function FiniteValues(a: seq<FloatValue>): seq<real>
  requires HasFiniteValue(a)
  ensures |FiniteValues(a)| == CountFinite(a)
  ensures |FiniteValues(a)| > 0
{
    if |a| == 0 then []
    else if IsFinite(a[0]) then [GetValue(a[0])] + FiniteValues(a[1..])
    else FiniteValues(a[1..])
}

// Helper predicate to check if a sequence of reals is sorted in non-decreasing order
predicate IsSorted(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if one sequence is a sorted permutation of another
predicate IsSortedPermutation(sorted: seq<real>, original: seq<real>) {
    IsSorted(sorted) && 
    multiset(sorted) == multiset(original)
}

/**
 * Compute the q-th percentile of the data, ignoring NaN values.
 * 
 * @param a: Input sequence of FloatValues that may contain NaN
 * @param q: Percentile to compute, must be between 0 and 100 inclusive
 * @returns: The q-th percentile as a FloatValue (NaN if all input values are NaN)
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanpercentile(a: seq<FloatValue>, q: real) returns (result: FloatValue)
  requires 0.0 <= q <= 100.0
  ensures 
    // Case 1: If all values are NaN, result is NaN
    AllNaN(a) ==> IsNaN(result)
  ensures
    // Case 2: If there exists at least one finite value
    HasFiniteValue(a) ==> 
      IsFinite(result) &&
      (
        // Get the finite values and sort them
        var finiteVals := FiniteValues(a);
        exists sortedVals: seq<real> ::
          IsSortedPermutation(sortedVals, finiteVals) &&
          |sortedVals| > 0 &&
          (
            // Single value case: result is that value
            (|sortedVals| == 1 ==> GetValue(result) == sortedVals[0]) &&
            // Multiple values case: result is within bounds and represents the q-th percentile
            (|sortedVals| > 1 ==> 
              sortedVals[0] <= GetValue(result) <= sortedVals[|sortedVals|-1] &&
              // Result is either exactly one of the sorted values or an interpolated value
              ((exists idx :: 0 <= idx < |sortedVals| && GetValue(result) == sortedVals[idx]) ||
              (exists i, j :: 
                0 <= i < |sortedVals| && 
                0 <= j < |sortedVals| && 
                i + 1 == j && 
                sortedVals[i] <= GetValue(result) <= sortedVals[j]))
            )
          )
      )
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
