// ATOM 
spec fn power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * power(n - 1) }
}

pub fn compute_power1(N: int) -> (y: nat)
    requires(N >= 0)
    ensures(y == power(N))
{
}

pub fn max(a: &[nat]) -> (m: int)
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i] <= m)
    ensures((m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i])
{
}

pub fn cube(n: nat) -> (c: nat)
    ensures(c == n * n * n)
{
}