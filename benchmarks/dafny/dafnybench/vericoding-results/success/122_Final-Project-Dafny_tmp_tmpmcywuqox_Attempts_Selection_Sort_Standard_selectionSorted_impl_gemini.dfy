// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < Array.Length
    invariant 0 <= i <= Array.Length
    invariant multiset(Array[..]) == multiset(old(Array[..]))
  {
    if i + 1 < Array.Length {
      var min_index := i;
      var j := i + 1;
      while j < Array.Length
        invariant i < j <= Array.Length
        invariant i <= min_index < j
        invariant forall k :: i <= k < j ==> Array[min_index] <= Array[k]
      {
        if Array[j] < Array[min_index] {
          min_index := j;
        }
        j := j + 1;
      }
      var temp := Array[i];
      Array[i] := Array[min_index];
      Array[min_index] := temp;
    }
    i := i + 1;
  }
}
// </vc-code>
