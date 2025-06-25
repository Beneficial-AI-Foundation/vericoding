spec fn Power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

pub fn ComputePower1(N: int) -> (y: nat)
    requires(N >= 0)
    ensures(y == Power(N as nat))
{
}

pub fn Max(a: &[nat]) -> (m: int)
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i] <= m)
    ensures((m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i])
{
}

pub fn Cube(n: nat) -> (c: nat)
    ensures(c == n * n * n)
{
}

pub fn IncrementMatrix(a: &mut [[int]])
    ensures(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[0].len() ==> a[i][j] == old(a)[i][j] + 1)
{
}

pub fn CopyMatrix(src: &[[int]], dst: &mut [[int]])
    requires(src.len() == dst.len() && src[0].len() == dst[0].len())
    ensures(forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[0].len() ==> dst[i][j] == old(src)[i][j])
{
}

pub fn DoubleArray(src: &[int], dst: &mut [int])
    requires(src.len() == dst.len())
    ensures(forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * old(src)[i])
{
}

pub fn RotateLeft(a: &mut [int])
    requires(a.len() > 0)
    ensures(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] == old(a)[(i+1) as int])
    ensures(a[a.len()-1] == old(a)[0])
{
}