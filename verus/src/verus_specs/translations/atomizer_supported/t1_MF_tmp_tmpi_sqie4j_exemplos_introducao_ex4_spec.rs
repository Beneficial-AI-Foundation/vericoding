spec fn Fat(n: nat) -> nat {
    if n == 0 { 1 } else { n * Fat((n - 1) as nat) }
}

pub fn Fatorial(n: nat) -> (r: nat)
    ensures r == Fat(n)
{
}