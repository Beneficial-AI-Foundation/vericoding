//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

// 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

// 3.
//IMPL maxArray
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
  max := arr[0];
  var index := 0;
  /* code modified by LLM (iteration 2): added maxIndex variable to track position of maximum element */
  var maxIndex := 0;
  
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall i: int :: 0 <= i < index ==> arr[i] <= max
    /* code modified by LLM (iteration 2): fixed invariant to use maxIndex which tracks actual position of max element found so far */
    invariant 0 <= maxIndex < arr.Length && arr[maxIndex] == max
    /* code modified by LLM (iteration 2): corrected invariant to allow maxIndex == index, fixing the case when index is 0 */
    invariant maxIndex <= index
  {
    if arr[index] > max {
      max := arr[index];
      /* code modified by LLM (iteration 2): update maxIndex when we find a new maximum */
      maxIndex := index;
    }
    index := index + 1;
  }
}

// 6
//ATOM_PLACEHOLDER_sum

//ATOM_PLACEHOLDER_sumBackwards