spec fn power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

pub fn compute_power(n: int) -> (y: nat)
    requires(n >= 0)
    ensures(y == power(n as nat))
{
}