spec fn factorial(n: nat) -> nat {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}

pub fn compute_factorial(n: int) -> (u: int)
    requires(1 <= n)
    ensures(u == factorial(n))
{
}