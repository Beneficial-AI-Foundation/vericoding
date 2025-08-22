
//Problem01
// ATOM 

//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}


// SPEC 

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
}

//# 2 pts

//Problem02
//ATOM_PLACEHOLDER_fact

//ATOM_PLACEHOLDER_factIter 
//# 3 pts
//Problem03
//ATOM_PLACEHOLDER_gcd

//ATOM_PLACEHOLDER_gcdI
//# 3 pts


// # sum: 9 pts















//# 3 pts


// # sum: 9 pts














