spec fn fat(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * fat(n - 1) }
}

pub fn fatorial(n: nat) -> (f: nat)
    ensures f == fat(n)
{
}