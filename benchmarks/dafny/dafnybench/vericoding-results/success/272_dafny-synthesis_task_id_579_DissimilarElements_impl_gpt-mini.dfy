predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    var x := a[i];
    if !(exists j :: 0 <= j < b.Length && b[j] == x) {
      if !(exists k :: 0 <= k < |res| && res[k] == x) {
        res := res + [x];
      }
    }
    i := i + 1;
  }

  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    var x := b[i];
    if !(exists j :: 0 <= j < a.Length && a[j] == x) {
      if !(exists k :: 0 <= k < |res| && res[k] == x) {
        res := res + [x];
      }
    }
    i := i + 1;
  }

  return res;
}
// </vc-code>

