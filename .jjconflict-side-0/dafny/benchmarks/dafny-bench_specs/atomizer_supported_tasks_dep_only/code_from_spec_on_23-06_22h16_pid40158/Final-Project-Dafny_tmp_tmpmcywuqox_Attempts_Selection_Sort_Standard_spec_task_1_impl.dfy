//IMPL selectionSorted
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var n := Array.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant multiset(old(Array[..])) == multiset(Array[..])
  {
    // Find minimum element in Array[i..n)
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> Array[minIndex] <= Array[k]
      invariant multiset(old(Array[..])) == multiset(Array[..])
    {
      if Array[j] < Array[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap Array[i] and Array[minIndex]
    if i != minIndex {
      var temp := Array[i];
      Array[i] := Array[minIndex];
      Array[minIndex] := temp;
    }
    
    i := i + 1;
  }
}