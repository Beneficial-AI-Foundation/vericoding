spec fn fib(n: nat) -> nat {
    if n == 0 { 1 } else
    if n == 1 { 1 } else
    fib((n - 1) as nat) + fib((n - 2) as nat)
}

pub fn Fib(n: nat) -> (r: nat)
    ensures(r == fib(n))
{
}