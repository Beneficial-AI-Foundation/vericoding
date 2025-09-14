predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall y :: y in seen <==> y in res
    invariant |res| == |seen|
    invariant forall x :: x in seen ==> (exists k :: 0 <= k < i && a[k] == x && !InArray(b, x))
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    var x := a[i];
    if (!InArray(b, x) && !(x in seen)) {
      res := res + [x];
      seen := seen + {x};
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

