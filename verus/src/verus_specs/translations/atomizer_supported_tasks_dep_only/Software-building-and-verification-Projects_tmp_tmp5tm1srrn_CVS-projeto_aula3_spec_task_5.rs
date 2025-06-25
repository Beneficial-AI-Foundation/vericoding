fn sum(n: nat) -> nat {
    if n == 0 { 0 } else { n + sum((n - 1) as nat) }
}

pub fn sumBackwards(n: nat) -> (r: nat)
    ensures r == sum(n)
{
}