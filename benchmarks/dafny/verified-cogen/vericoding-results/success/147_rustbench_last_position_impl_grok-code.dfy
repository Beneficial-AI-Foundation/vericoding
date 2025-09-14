// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(a: array<int>, elem: int) returns (result: int)
    requires 0 < a.Length < 100_000
    requires exists i :: 0 <= i < a.Length && a[i] == elem
    ensures 0 <= result < a.Length
    ensures forall i :: result < i < a.Length ==> a[i] != elem
    ensures a[result] == elem
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): looping from the end to find last position, removing assumption bypass */
  var i := a.Length - 1;
  while i >= 0 && a[i] != elem 
    invariant -1 <= i < a.Length
    invariant forall k :: i < k < a.Length ==> a[k] != elem
  {
    i := i - 1;
  }
  result := i;
}
// </vc-code>
