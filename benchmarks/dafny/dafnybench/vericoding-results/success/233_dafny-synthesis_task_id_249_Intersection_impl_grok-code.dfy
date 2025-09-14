predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// No additional helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var temp := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |temp| ==> InArray(a, temp[k]) && InArray(b, temp[k])
    invariant forall k, m :: 0 <= m < k < |temp| ==> temp[m] != temp[k]
  {
    var elem := a[i];
    if InArray(b, elem) && !(elem in temp) {
      temp := temp + [elem];
    }
    i := i + 1;
  }
  result := temp;
}
// </vc-code>

