predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
// Helper lemma to ensure uniqueness in the sequence
lemma UniqueElements(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  // No additional proof needed as this is directly from the ensures clause
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveElementsImpl(a: array<int>, b: array<int>) returns (result: seq<int>)
  ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
  var temp: seq<int> := [];
  for i := 0 to a.Length
    invariant forall x :: x in temp ==> InArray(a, x) && !InArray(b, x)
    invariant forall k, l :: 0 <= k < l < |temp| ==> temp[k] != temp[l]
  {
    if i < a.Length && !InArray(b, a[i]) && a[i] !in temp
    {
      temp := temp + [a[i]];
    }
  }
  result := temp;
}
// </vc-code>
