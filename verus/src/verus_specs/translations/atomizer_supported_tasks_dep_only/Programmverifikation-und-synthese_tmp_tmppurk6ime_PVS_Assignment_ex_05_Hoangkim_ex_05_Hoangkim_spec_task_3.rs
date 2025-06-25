spec fn gcd(m: nat, n: nat) -> nat
    recommends m > 0 && n > 0
{
    if m == n { m }
    else if m > n { gcd((m - n) as nat, n) }
    else { gcd(m, (n - m) as nat) }
}

pub fn gcdI(m: int, n: int) -> (g: int)
    requires m > 0 && n > 0
    ensures g == gcd(m as nat, n as nat)
{
}