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
lemma ToNumericOfRealIsIdentity(x: real)
    ensures ToNumeric(Real(x)) == x
{
}

lemma SumUpToRecursion(a: seq<FloatValue>, i: int)
    requires 0 < i < |a|
    ensures SumUpTo(a, i) == SumUpTo(a, i-1) + ToNumeric(a[i])
{
}
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
  var n := |a|;
  var res: seq<FloatValue> := [];
  var prev: real := 0.0;
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == Real(SumUpTo(a, k))
    invariant forall k :: 1 <= k < i ==> res[k] == Real(ToNumeric(res[k-1]) + ToNumeric(a[k]))
    invariant forall k :: 0 <= k < i ==> !IsNaN(res[k])
    invariant i == 0 ==> prev == 0.0
    invariant i > 0 ==> prev == ToNumeric(res[i-1])
    invariant i > 0 ==> prev == SumUpTo(a, i-1)
  {
    var x := Real(prev + ToNumeric(a[i]));
    res := res + [x];
    prev := prev + ToNumeric(a[i]);
    i := i + 1;
  }
  result := res;
}
// </vc-code>
