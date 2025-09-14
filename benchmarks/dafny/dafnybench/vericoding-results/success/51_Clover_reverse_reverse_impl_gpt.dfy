

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  ghost var oldA := a[..];
  var i := 0;
  var j := a.Length - 1;
  while i < j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant i + j == a.Length - 1
    invariant forall k :: 0 <= k < i ==> a[k] == oldA[a.Length - 1 - k]
    invariant forall k :: j < k < a.Length ==> a[k] == oldA[a.Length - 1 - k]
    invariant forall k :: i <= k <= j ==> a[k] == oldA[k]
    decreases j - i
  {
    var t := a[i];
    a[i] := a[j];
    a[j] := t;
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

