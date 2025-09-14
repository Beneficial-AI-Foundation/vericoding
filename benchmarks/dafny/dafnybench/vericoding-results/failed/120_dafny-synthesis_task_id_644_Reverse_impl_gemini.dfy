// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Switched to a while-loop implementation to rule out non-verification related toolchain issues. */
  var i := 0;
  var j := a.Length - 1;
  while i < j
    invariant 0 <= i <= a.Length && -1 <= j < a.Length
    invariant i + j == a.Length - 1
    invariant forall k :: (0 <= k < i || j < k < a.Length) ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    decreases j - i
  {
      var tmp := a[i];
      a[i] := a[j];
      a[j] := tmp;
      i := i + 1;
      j := j - 1;
  }
}
// </vc-code>
