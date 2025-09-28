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
/* helper modified by LLM (iteration 3): [Completed the inductive proof in the lemma body.] */
lemma AllNaNImpliesProductIsOne(arr: seq<FloatValue>, i: nat)
    requires i < |arr|
    requires AllNaNUpTo(arr, i)
    ensures CumulativeProduct(arr, i) == 1.0
    decreases i
{
    if i > 0 {
        AllNaNImpliesProductIsOne(arr, i-1);
    }
}
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
  /* code modified by LLM (iteration 3): [Added asserts and a final forall block to guide the verifier.] */
  var result_arr := new FloatValue[|arr|];

  if |arr| > 0 {
    var i: nat := 0;
    var prod: real := 1.0;
    while i < |arr|
      invariant 0 <= i <= |arr|
      invariant prod == (if i == 0 then 1.0 else CumulativeProduct(arr, i - 1))
      invariant forall j :: 0 <= j < i ==> result_arr[j] == Real(CumulativeProduct(arr, j))
      decreases |arr| - i
    {
      prod := prod * GetValueOrOne(arr[i]);
      assert prod == CumulativeProduct(arr, i);
      result_arr[i] := Real(prod);
      i := i + 1;
    }
  }
  result := result_arr[..];

  // After the loop, we know result[k] == Real(CumulativeProduct(arr, k)) for all k.
  // This proves the second primary ensures clause.
  // Now, use that fact along with the lemma to prove the first ensures clause.
  forall k | 0 <= k < |arr|
    ensures (AllNaNUpTo(arr, k) ==> result[k] == Real(1.0)) &&
            (!AllNaNUpTo(arr, k) ==> result[k] == Real(CumulativeProduct(arr,k))) &&
            !IsNaN(result[k])
  {
    assert result[k] == Real(CumulativeProduct(arr, k));
    if AllNaNUpTo(arr, k) {
      AllNaNImpliesProductIsOne(arr, k);
      assert CumulativeProduct(arr, k) == 1.0;
    }
  }
}
// </vc-code>
