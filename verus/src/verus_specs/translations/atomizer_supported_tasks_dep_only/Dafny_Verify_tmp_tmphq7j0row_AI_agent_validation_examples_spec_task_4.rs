// ATOM 
spec fn Power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

pub fn Max(a: &[nat]) -> i32
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i] <= result)
    ensures((result == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && result == a[i])
{
}

pub fn Cube(n: nat) -> nat
    ensures(result == n * n * n)
{
}

pub fn IncrementMatrix(a: &mut [[i32]])
    ensures(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[0].len() ==> a[i][j] == old(a)[i][j] + 1)
{
}