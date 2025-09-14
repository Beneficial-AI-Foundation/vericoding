

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// <vc-code>
{
  var n := Array.Length;
  if n < 2 {
    return;
  }
  for i := 0 to n - 1
    invariant multiset(Array[..]) == multiset(old(Array[..]))
  {
    var minIndex := i;
    for j := i + 1 to n - 1
      invariant 0 <= minIndex <= n - 1
    {
      if Array[j] < Array[minIndex]
      {
        minIndex := j;
      }
    }
    Array[i], Array[minIndex] := Array[minIndex], Array[i];
  }
}
// </vc-code>

