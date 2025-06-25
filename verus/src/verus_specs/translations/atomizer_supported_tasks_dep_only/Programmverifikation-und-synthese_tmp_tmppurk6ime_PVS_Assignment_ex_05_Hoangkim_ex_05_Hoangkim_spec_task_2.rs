//Problem01
//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_fibIter
//# 2 pts

//Problem02
// ATOM 
//# 2 pts

//Problem02
spec fn fact(n: nat) -> nat
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// SPEC 

pub fn factIter(n: nat) -> (a: nat)
    requires(n >= 0)
    ensures(a == fact(n))
{
}
 
//# 3 pts
//Problem03
//ATOM_PLACEHOLDER_gcd

//ATOM_PLACEHOLDER_gcdI
//# 3 pts


// # sum: 9 pts















//# 3 pts


// # sum: 9 pts