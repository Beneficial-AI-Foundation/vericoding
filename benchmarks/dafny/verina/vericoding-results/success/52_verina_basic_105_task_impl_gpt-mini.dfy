// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): relate array slice length to array length */
lemma ArraySliceLength(arr: array<int>)
  ensures |arr[..]| == arr.Length
{
}

/* helper modified by LLM (iteration 2): relate array slice indexing to array indexing */
lemma ArraySliceIndex(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  ensures arr[..][i] == arr[i]
{
}

// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute element-wise product without trailing semicolons in invariants */
  var arr := new int[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> arr[k] == a[k] * b[k]
  {
    arr[i] := a[i] * b[i];
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
