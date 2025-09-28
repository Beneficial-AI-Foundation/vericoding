// <vc-preamble>
// Take elements from a source array at specified indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use sequence-length notation for array slice */
lemma ArraySliceLength<T>(a: array<T>)
  ensures |a[..]| == a.Length
{
  var s := a[..];
  assert |s| == a.Length;
}

// </vc-helpers>

// <vc-spec>
method Take(arr: seq<real>, indices: seq<int>) returns (result: seq<real>)
  // All indices must be valid positions in the source array
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |arr|
  // Result has the same length as the indices array
  ensures |result| == |indices|
  // Each element in result comes from the corresponding indexed position in arr
  ensures forall i :: 0 <= i < |indices| ==> result[i] == arr[indices[i]]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct array from indices and return its slice */
  var arrLen := |indices|;
  var a := new real[arrLen];
  var i := 0;
  while i < arrLen
    invariant 0 <= i <= arrLen
    invariant forall j :: 0 <= j < i ==> a[j] == arr[indices[j]]
  {
    a[i] := arr[indices[i]];
    i := i + 1;
  }
  ArraySliceLength(a);
  result := a[..];
}

// </vc-code>
