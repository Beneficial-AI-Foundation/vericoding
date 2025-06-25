// ATOM 

spec fn gcd_prime(x: int, y: int) -> int
    requires x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd_prime(y, x) }
}

// SPEC 

pub fn gcdI(m: int, n: int) -> (d: int)
    requires(m > 0 && n > 0)
    ensures(|d: int| d == gcd(m, n))
{
}

// ATOM 

spec fn gcd_prime(x: int, y: int) -> int
    requires x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd_prime(y, x) }
}