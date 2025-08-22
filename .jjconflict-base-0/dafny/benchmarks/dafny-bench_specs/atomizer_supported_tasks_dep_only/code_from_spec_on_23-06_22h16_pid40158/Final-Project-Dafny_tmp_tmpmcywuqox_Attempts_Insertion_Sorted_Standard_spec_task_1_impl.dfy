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
    
    /* code modified by LLM (iteration 3): Fixed inner loop with correct invariants for insertion sort */
    while j >= 0 && Array[j] > key
      invariant -1 <= j < i
      invariant InsertionSorted(Array, 0, j + 1)
      invariant forall k :: j + 2 <= k <= i ==> Array[k] == old(Array[k])
      invariant forall k :: j + 2 <= k <= i ==> Array[k] >= key
      invariant forall k :: 0 <= k <= j ==> Array[k] <= key || Array[k] == old(Array[k])
      decreases j
    {
      Array[j + 1] := Array[j];
      j := j - 1;
    }
    
    Array[j + 1] := key;
    
    /* code modified by LLM (iteration 3): Added helper assertions to prove sorted property */
    assert forall k :: 0 <= k <= j ==> Array[k] <= Array[j + 1];
    assert forall k :: j + 2 <= k <= i ==> Array[j + 1] <= Array[k];
    assert InsertionSorted(Array, 0, j + 1);
    assert InsertionSorted(Array, j + 1, i + 1);
    
    /* code modified by LLM (iteration 3): Prove the combined sorted property */
    forall x, y | 0 <= x < y <= i {
      if y <= j + 1 {
        assert Array[x] <= Array[y];
      } else if x <= j {
        assert Array[x] <= Array[j + 1] <= Array[y];
      } else {
        assert Array[x] <= Array[y];
      }
    }
    
    i := i + 1;
  }
}