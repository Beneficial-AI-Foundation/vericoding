

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// <vc-code>
{
  diff := [];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in diff ==> (x in a && x !in b)
    invariant forall x :: x in a[..i] && x !in b ==> x in diff
    invariant forall j, k :: 0 <= j < k < |diff| ==> diff[j] != diff[k]
    invariant forall x :: x in diff ==> exists idx :: 0 <= idx < i && a[idx] == x
  {
    if a[i] !in b && a[i] !in diff {
      diff := diff + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

