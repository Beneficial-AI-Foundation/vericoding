pub fn exp_by_sqr(x0: real, n0: nat) -> (r: real)
    requires(x0 >= 0.0)
    ensures(r == exp(x0, n0))
{
}

spec fn exp(x: real, n: nat) -> real
{
    if n == 0 { 1.0 }
    else if x == 0.0 { 0.0 }
    else if n == 0 && x == 0.0 { 1.0 }
    else { x * exp(x, (n - 1) as nat) }
}