//Problem01
//a)
// ATOM 

//b)
spec fn gcd_prime(x: int, y: int) -> int
    recommends x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd(y, x) }
}

// SPEC 

pub fn gcdI(m: int, n: int) -> (d: int)
    requires(m > 0 && n > 0)
    ensures(d == gcd(m, n))
{
}

//b)
// ATOM 

//b)
spec fn gcd_prime(x: int, y: int) -> int
    recommends x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd(y, x) }
}