// 1 a)

// [ai, aj[
// ATOM 
// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}


// 1 b)
// SPEC 

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
}


// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
// SPEC 

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
}
Fast

//ATOM_PLACEHOLDER_is_prefix_sum_for

//ATOM_PLACEHOLDER_proof//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_from_array

//ATOM_PLACEHOLDER_mem

