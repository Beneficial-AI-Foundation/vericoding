// <vc-preamble>
// Datatype to represent floating point values that can be NaN or real numbers
datatype FloatValue = NaN | Real(value: real)

// Helper predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
    f.NaN?
}

// Helper function to get the numeric value, treating NaN as 0
function ToNumeric(f: FloatValue): real
{
    match f
    case NaN => 0.0
    case Real(v) => v
}

// Helper function to sum a sequence of FloatValues up to a given index (inclusive)
function SumUpTo(a: seq<FloatValue>, index: int): real
    requires 0 <= index < |a|
{
    if index == 0 then ToNumeric(a[0])
    else SumUpTo(a, index - 1) + ToNumeric(a[index])
}

// Main method for computing cumulative sum with NaN handling
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NanCumSum(a: seq<FloatValue>) returns (result: seq<FloatValue>)
    // No preconditions needed - handles any input sequence
    ensures |result| == |a|
    // For non-empty sequences, first element is either a[0] or 0 if a[0] is NaN
    ensures |a| > 0 ==> (IsNaN(a[0]) ==> result[0] == Real(0.0))
    ensures |a| > 0 ==> (!IsNaN(a[0]) ==> result[0] == a[0])
    // Recurrence relation: each element is previous cumsum + current element (or 0 if NaN)
    ensures forall i :: 1 <= i < |a| ==> 
        result[i] == Real(ToNumeric(result[i-1]) + ToNumeric(a[i]))
    // Cumulative sum property: each element equals sum of all previous non-NaN elements
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == Real(SumUpTo(a, i))
    // Result never contains NaN (NaNs are replaced with 0 contribution)
    ensures forall i :: 0 <= i < |result| ==> !IsNaN(result[i])
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    result := [];
  } else {
    result := [];
    var cumsum := ToNumeric(a[0]);
    result := result + [Real(cumsum)];
    
    var i := 1;
    while i < |a|
      invariant 1 <= i <= |a|
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == Real(SumUpTo(a, j))
      invariant forall j :: 0 <= j < |result| ==> !IsNaN(result[j])
      invariant cumsum == ToNumeric(result[i-1])
    {
      cumsum := cumsum + ToNumeric(a[i]);
      result := result + [Real(cumsum)];
      i := i + 1;
    }
  }
}
// </vc-code>
