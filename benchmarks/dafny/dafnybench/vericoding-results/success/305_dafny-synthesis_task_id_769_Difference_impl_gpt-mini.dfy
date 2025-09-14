

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| <= i
    invariant forall x :: x in res <==> exists k :: 0 <= k < i && a[k] == x && a[k] !in b
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    var x := a[i];
    if x !in b && x !in res {
      res := res + [x];
    }
    i := i + 1;
  }
  diff := res;
}
// </vc-code>

