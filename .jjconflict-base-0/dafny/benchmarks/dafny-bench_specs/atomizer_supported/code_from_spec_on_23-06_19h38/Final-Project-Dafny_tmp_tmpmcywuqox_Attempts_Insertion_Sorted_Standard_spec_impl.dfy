// ATOM 
predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

//IMPL sorting
method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
{
  var i := 1;
  while i < Array.Length
    invariant 1 <= i <= Array.Length
    invariant InsertionSorted(Array, 0, i)
  {
    var key := Array[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 2): Simplified loop invariants to maintain basic bounds and preserve sorted portion */
    while j >= 0 && Array[j] > key
      invariant -1 <= j < i
      invariant forall k :: j + 2 <= k <= i ==> Array[k] >= key
      invariant forall k :: 0 <= k <= j ==> Array[k] <= Array[k+1]
    {
      Array[j + 1] := Array[j];
      j := j - 1;
    }
    
    Array[j + 1] := key;
    i := i + 1;
  }
}