

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
  for i := 0 to n
    invariant multiset(Array[..]) == multiset(old(Array[..]))
  {
    var minIndex := i;
    for j := i+1 to n
      invariant i <= minIndex < n
    {
      if Array[j] < Array[minIndex] {
        minIndex := j;
      }
    }
    var temp := Array[i];
    Array[i] := Array[minIndex];
    Array[minIndex] := temp;
  }
}
// </vc-code>

