// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function UpdateVal(v: int, x: int, y: int): int { if v == x then y else v }
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
  ghost var A0 := a[..];
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> (if A0[k] == x then a[k] == y else a[k] == A0[k])
    invariant forall k :: i <= k < a.Length ==> a[k] == A0[k]
    decreases a.Length - i
  {
    if a[i] == x {
      a[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>
