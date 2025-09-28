// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide sequence view of array without redundant null check */
function OldSeq(a: array<int>): seq<int>
  reads a
{
  a[..]
}
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
  /* code modified by LLM (iteration 2): implement replace using snapshot and strengthen invariants to help verifier */
  var oldSeq := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i && oldSeq[k] == x ==> a[k] == y
    invariant forall k :: 0 <= k < i && oldSeq[k] != x ==> a[k] == oldSeq[k]
    invariant forall k :: i <= k < a.Length ==> a[k] == oldSeq[k]
  {
    if oldSeq[i] == x {
      a[i] := y;
    }
    assert if oldSeq[i] == x then a[i] == y else a[i] == oldSeq[i];
    i := i + 1;
  }
}
// </vc-code>
