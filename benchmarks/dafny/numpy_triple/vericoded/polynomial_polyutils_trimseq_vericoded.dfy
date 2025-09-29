// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added trivial lemma to keep helpers section valid */
lemma TrivialArrayLengthLemma(arr: array<real>)
  ensures arr.Length == arr.Length
{
}

// </vc-helpers>

// <vc-spec>
method TrimSeq(arr: array<real>) returns (result: array<real>)
  requires arr.Length >= 0
  ensures result.Length == arr.Length
  // If sequence is empty, return empty sequence
  ensures arr.Length == 0 ==> result.Length == 0
  // If last element is non-zero, return sequence unchanged
  ensures arr.Length > 0 && arr[arr.Length - 1] != 0.0 ==> 
    (forall i :: 0 <= i < arr.Length ==> result[i] == arr[i])
  // If last element is zero, trim properly
  ensures arr.Length > 0 && arr[arr.Length - 1] == 0.0 ==> 
    (exists k :: 0 <= k < arr.Length &&
      // All elements after k in original sequence are zero
      (forall j :: k < j < arr.Length ==> arr[j] == 0.0) &&
      // Result preserves elements up to k, zeros after
      (forall i :: 0 <= i <= k ==> result[i] == arr[i]) &&
      (forall i :: k < i < arr.Length ==> result[i] == 0.0) &&
      // Element at k is non-zero unless k = 0 and all elements are zero
      (k > 0 ==> arr[k] != 0.0) &&
      // If k = 0, then either arr[0] != 0 or all elements in arr are zero
      (k == 0 ==> (arr[0] != 0.0 || (forall j :: 0 <= j < arr.Length ==> arr[j] == 0.0))))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): return alias and prove existential via ghost search of last non-zero */
  result := arr;
  if arr.Length > 0 && arr[arr.Length - 1] == 0.0 {
    var i := 0;
    ghost var k := 0;
    ghost var found := false;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant 0 <= k < arr.Length
      invariant (!found ==> (forall j :: 0 <= j < i ==> arr[j] == 0.0))
      invariant (found ==> (0 <= k < i && arr[k] != 0.0 && (forall j :: k < j < i ==> arr[j] == 0.0)))
      decreases arr.Length - i
    {
      if arr[i] != 0.0 {
        k := i;
        found := true;
      }
      i := i + 1;
    }
    if found {
      ghost var kk := k;
      assert 0 <= kk < arr.Length;
      assert (forall j :: kk < j < arr.Length ==> arr[j] == 0.0);
      assert forall i0 :: 0 <= i0 <= kk ==> result[i0] == arr[i0];
      assert forall i0 :: kk < i0 < arr.Length ==> result[i0] == 0.0;
      assert kk > 0 ==> arr[kk] != 0.0;
      assert kk == 0 ==> arr[0] != 0.0;
    } else {
      ghost var kk := 0;
      assert 0 <= kk < arr.Length;
      assert forall j :: kk < j < arr.Length ==> arr[j] == 0.0;
      assert forall i0 :: 0 <= i0 <= kk ==> result[i0] == arr[i0];
      assert forall i0 :: kk < i0 < arr.Length ==> result[i0] == 0.0;
      assert kk == 0 ==> (arr[0] != 0.0 || (forall j :: 0 <= j < arr.Length ==> arr[j] == 0.0));
    }
  }
}

// </vc-code>
