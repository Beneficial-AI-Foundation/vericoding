// <vc-preamble>
// Datatype to represent floating point values that may be NaN
datatype FloatValue = NaN | Real(value: real)

// Helper predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
    f.NaN?
}

// Helper function to get the real value, treating NaN as 1.0
function GetValueOrOne(f: FloatValue): real
{
    if f.NaN? then 1.0 else f.value
}

// Helper function to compute product of non-NaN elements up to position i
function CumulativeProduct(arr: seq<FloatValue>, i: nat): real
    requires i < |arr|
{
    if i == 0 then
        GetValueOrOne(arr[0])
    else
        CumulativeProduct(arr, i-1) * GetValueOrOne(arr[i])
}

// Helper predicate to check if all elements up to position i are NaN
predicate AllNaNUpTo(arr: seq<FloatValue>, i: nat)
    requires i < |arr|
{
    forall j :: 0 <= j <= i ==> IsNaN(arr[j])
}

// Main method specification for nancumprod
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NanCumprod(arr: seq<FloatValue>) returns (result: seq<FloatValue>)
    ensures |result| == |arr|
    ensures forall i :: 0 <= i < |arr| ==>
        // If all elements from start to i are NaN, result[i] = 1.0
        (AllNaNUpTo(arr, i) ==> result[i] == Real(1.0)) &&
        // Otherwise, result[i] = cumulative product treating NaN as 1.0
        (!AllNaNUpTo(arr, i) ==> result[i] == Real(CumulativeProduct(arr, i))) &&
        // Result is never NaN (since NaN is treated as 1.0)
        !IsNaN(result[i])
    ensures forall i :: 0 <= i < |arr| ==>
        // General property: each result element is the product of non-NaN elements up to that position
        result[i] == Real(CumulativeProduct(arr, i))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
