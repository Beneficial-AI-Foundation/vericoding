pub fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires(m > 0 && n > 0)
    ensures(res == gcd(m, n))
{
}

spec fn gcd(m: nat, n: nat) -> nat
    recommends(m > 0 && n > 0)
{
    if m == n { n }
    else if m > n { gcd((m - n) as nat, n) }
    else { gcd(m, (n - m) as nat) }
}