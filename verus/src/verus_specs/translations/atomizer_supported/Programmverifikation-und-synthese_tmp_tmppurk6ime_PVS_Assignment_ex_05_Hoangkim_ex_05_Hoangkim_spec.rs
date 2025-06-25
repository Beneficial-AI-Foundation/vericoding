//Problem01
// ATOM 

//Problem01
spec fn fib(n: nat) -> nat
{
    if n < 2 { n } else { fib((n-2) as nat) + fib((n-1) as nat) }
}

// SPEC 

pub fn fibIter(n: nat) -> (a: nat)
    requires(n > 0)
    ensures(a == fib(n))
{
}

//# 2 pts

//Problem02
// ATOM 
//# 2 pts

//Problem02
spec fn fact(n: nat) -> nat
{
    if n == 0 { 1 } else { n * fact((n-1) as nat) }
}

// SPEC 

pub fn factIter(n: nat) -> (a: nat)
    requires(n >= 0)
    ensures(a == fact(n))
{
}
 
//# 3 pts
//Problem03
// ATOM 
//# 3 pts
//Problem03
spec fn gcd(m: nat, n: nat) -> nat
    requires(m > 0 && n > 0)
{
    if m == n { m }
    else if m > n { gcd((m - n) as nat, n) }
    else { gcd(m, (n - m) as nat) }
}

// SPEC 

pub fn gcdI(m: int, n: int) -> (g: int)
    requires(m > 0 && n > 0)
    ensures(g == gcd(m, n))
{
}

//# 3 pts


// # sum: 9 pts















//# 3 pts


// # sum: 9 pts