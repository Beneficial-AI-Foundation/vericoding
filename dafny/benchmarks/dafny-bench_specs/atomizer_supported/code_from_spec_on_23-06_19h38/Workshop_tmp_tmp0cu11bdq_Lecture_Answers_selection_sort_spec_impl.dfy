//https://homepage.cs.uiowa.edu/~tinelli/classes/181/Fall21/Tools/Dafny/Examples/selection-sort.shtml

//ATOM 
predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

//ATOM
predicate sorted(a: array<int>)
	requires a != null
	reads a
{
	sorted'(a, a.Length)
}

//IMPL Selection sort on arrays
method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  //ensures multiset(old(a[..])) == multiset(a[..])
{
  if a == null || a.Length <= 1 {
    return;
  }
  
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length
    invariant sorted'(a, i)
    invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i < j <= a.Length
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap elements at positions i and minIndex
    var temp := a[i];
    a[i] := a[minIndex];
    a[minIndex] := temp;
    
    i := i + 1;
  }
}