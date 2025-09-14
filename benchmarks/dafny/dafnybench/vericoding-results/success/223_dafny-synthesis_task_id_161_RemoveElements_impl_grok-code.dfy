predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in res ==> InArray(a, x) && !InArray(b, x)
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]
  {
    var elem := a[i];
    if !InArray(b, elem) && elem !in res {
      res := res + [elem];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

