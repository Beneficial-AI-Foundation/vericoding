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

//IMPL sumBackwards
method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == sum(i)
  {
    i := i + 1;
    r := r + i;
  }
}