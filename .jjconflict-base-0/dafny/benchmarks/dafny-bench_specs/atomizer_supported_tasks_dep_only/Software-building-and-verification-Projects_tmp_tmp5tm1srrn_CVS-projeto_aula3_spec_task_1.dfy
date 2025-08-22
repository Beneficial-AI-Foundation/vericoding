// ATOM 
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}


// SPEC 

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{
}


// 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

// 3.
//ATOM_PLACEHOLDER_maxArray

// 5.
//ATOM_PLACEHOLDER_maxArrayReverse

// 6
//ATOM_PLACEHOLDER_sum

//ATOM_PLACEHOLDER_sumBackwards

