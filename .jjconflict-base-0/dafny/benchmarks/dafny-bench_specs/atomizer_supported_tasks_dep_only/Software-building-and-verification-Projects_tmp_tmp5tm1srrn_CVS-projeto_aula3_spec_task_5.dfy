//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

// 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

// 3.
//ATOM_PLACEHOLDER_maxArray

// 5.
//ATOM_PLACEHOLDER_maxArrayReverse

// 6
// ATOM 

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}


// SPEC 

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
}


