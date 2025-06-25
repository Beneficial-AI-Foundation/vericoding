spec fn sum(n: nat) -> int {
    if n == 0 { 0 } else { n + sum((n - 1) as nat) }
}

pub fn Sum(n: nat) -> (s: int)
    ensures s == sum(n)
{
}