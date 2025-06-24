//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

// 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

// 3.
//ATOM_PLACEHOLDER_maxArray

// 5.
// SPEC 

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}


// 6
//ATOM_PLACEHOLDER_sum

//ATOM_PLACEHOLDER_sumBackwards

