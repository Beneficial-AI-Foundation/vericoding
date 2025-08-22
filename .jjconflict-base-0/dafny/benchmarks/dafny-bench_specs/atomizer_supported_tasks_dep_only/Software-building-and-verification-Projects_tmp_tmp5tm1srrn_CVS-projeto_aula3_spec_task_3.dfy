//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

// 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

// 3.
// SPEC 

// 3.
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}


// 5.
// SPEC 

// 3.
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}
Reverse

// 6
//ATOM_PLACEHOLDER_sum

//ATOM_PLACEHOLDER_sumBackwards

