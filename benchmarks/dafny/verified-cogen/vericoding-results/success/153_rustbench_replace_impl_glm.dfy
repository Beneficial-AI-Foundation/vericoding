// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method replace(a: array<int>, x: int, y: int)
    modifies a
    ensures
        forall k :: 0 <= k < a.Length && old(a[k]) == x ==> a[k] == y
    ensures
        forall k :: 0 <= k < a.Length && old(a[k]) != x ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariants to prove postconditions */
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < i && old(a[k]) == x ==> a[k] == y
    invariant forall k :: 0 <= k < i && old(a[k]) != x ==> a[k] == old(a[k])
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
  {
    if a[i] == x
    {
      a[i] := y;
    }
  }
}
// </vc-code>
