predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// Empty: no updates needed as invariants are adjusted in the code section.
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
  var temp: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall ii, jj :: 0 <= ii < jj < |temp| ==> temp[ii] != temp[jj]
    invariant forall x :: x in temp ==> InArray(a, x) != InArray(b, x)
  {
    var x := a[i];
    if !InArray(b, x) && !(exists k :: 0 <= k < |temp| && temp[k] == x) {
      temp := temp + [x];
    }
    i := i + 1;
  }
  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant forall ii, jj :: 0 <= ii < jj < |temp| ==> temp[ii] != temp[jj]
    invariant forall x :: x in temp ==> InArray(a, x) != InArray(b, x)
  {
    var x := b[i];
    if !InArray(a, x) && !(exists k :: 0 <= k < |temp| && temp[k] == x) {
      temp := temp + [x];
    }
    i := i + 1;
  }
  result := temp;
}
// </vc-code>

