//ATOM
function sum_up_to (n: nat): nat
{
 if (n == 0) then 0
 else sum_up_to (n-1) + 1
}


// SPEC


method SumUpTo (n: nat) returns (r: nat)
 ensures r == sum_up_to (n)
{
}
