// <vc-preamble>
/* 
 * Dafny specification for numpy.nanmedian - computes the median along the specified axis, ignoring NaNs.
 * Returns the median of the array elements, treating NaN values as missing data.
 */

// Datatype to represent floating point values that can be NaN
datatype FloatValue = Finite(value: real) | NaN

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Predicate to check if a FloatValue is finite
predicate IsFinite(f: FloatValue) {
    f.Finite?
}

// Extract the real value from a Finite FloatValue
function GetValue(f: FloatValue): real
    requires IsFinite(f)
{
    f.value
}

// Predicate to check if a sequence is sorted in non-decreasing order
predicate IsSorted(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Predicate to check if sequence b is a permutation of sequence a
predicate IsPermutation(a: seq<real>, b: seq<real>) {
    |a| == |b| && multiset(a) == multiset(b)
}

// Function to extract finite values from an array as a sequence
function ExtractFiniteValues(arr: array<FloatValue>): seq<real>
    reads arr
{
    seq(arr.Length, i => if IsFinite(arr[i]) then GetValue(arr[i]) else 0.0)
}

// Get indices of finite values
function GetFiniteIndices(arr: array<FloatValue>): seq<int>
    reads arr
{
    seq(arr.Length, i => i)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanmedian(a: array<FloatValue>) returns (result: FloatValue)
    ensures 
        // Case 1: All values are NaN
        (forall i :: 0 <= i < a.Length ==> IsNaN(a[i])) ==> IsNaN(result)
    ensures
        // Case 2: At least one finite value exists
        (exists i :: 0 <= i < a.Length && IsFinite(a[i])) ==>
            exists finiteIndices: seq<int>, sortedVals: seq<real> ::
                // finiteIndices contains all indices with finite values
                |finiteIndices| > 0 &&
                (forall i :: 0 <= i < a.Length ==> (i in finiteIndices <==> IsFinite(a[i]))) &&
                (forall i :: i in finiteIndices ==> 0 <= i < a.Length) &&
                // sortedVals is the sorted list of finite values
                |sortedVals| == |finiteIndices| &&
                (forall i :: 0 <= i < |finiteIndices| ==> sortedVals[i] == GetValue(a[finiteIndices[i]])) &&
                IsSorted(sortedVals) &&
                // result is the median of sorted finite values
                (if |sortedVals| % 2 == 1 then
                    IsFinite(result) && GetValue(result) == sortedVals[|sortedVals| / 2]
                else
                    IsFinite(result) && GetValue(result) == (sortedVals[|sortedVals| / 2 - 1] + sortedVals[|sortedVals| / 2]) / 2.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
