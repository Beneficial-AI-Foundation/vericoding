// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoWaySort(a: array<bool>)
    requires a.Length <= 100_000
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
    modifies a
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length - 1;
  
  while i < j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall k :: 0 <= k < i ==> !a[k]
    invariant forall k :: j < k < a.Length ==> a[k]
    invariant multiset(a[..]) == old(multiset(a[..])) 
  {
    if !a[i] {
      i := i + 1;
    } else if a[j] {
      j := j - 1;
    } else {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>
