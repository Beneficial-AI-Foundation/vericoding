// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(a: seq<int>) returns (result: bool)
    ensures
        result == (forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant to handle empty sequences */
  result := true;
  if |a| == 0 {
    return;
  }
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant result == (forall k :: 0 <= k < i ==> a[k] <= a[k + 1])
  {
    if a[i] > a[i + 1] {
      result := false;
      // No need to break, can continue but since result false, it doesn't matter
    }
    i := i + 1;
  }
}
// </vc-code>
