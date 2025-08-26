method findMinIndex(Array: array<int>, start: int) returns (minIndex: int)
  requires 0 <= start < Array.Length
  ensures start <= minIndex < Array.Length
  ensures forall k :: start <= k < Array.Length ==> Array[minIndex] <= Array[k]
{
  minIndex := start;
  var i := start + 1;
  
  while i < Array.Length
    invariant start <= minIndex < Array.Length
    invariant start + 1 <= i <= Array.Length
    invariant forall k :: start <= k < i ==> Array[minIndex] <= Array[k]
  {
    if Array[i] < Array[minIndex] {
      minIndex := i;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// <vc-code>
{
  if Array.Length <= 1 {
    return;
  }
  
  var i := 0;
  
  while i < Array.Length - 1
    invariant 0 <= i <= Array.Length - 1
    invariant multiset(old(Array[..])) == multiset(Array[..])
  {
    var minIndex := findMinIndex(Array, i);
    
    // Swap Array[i] and Array[minIndex]
    var temp := Array[i];
    Array[i] := Array[minIndex];
    Array[minIndex] := temp;
    
    i := i + 1;
  }
}
// </vc-code>