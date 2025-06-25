spec fn sum(n: nat) -> nat {
    if n == 0 { 0 } else { n + sum(n - 1) }
}

pub fn compute_sum(n: nat) -> (s: nat)
    ensures s == sum(n)
{
    todo!()
}