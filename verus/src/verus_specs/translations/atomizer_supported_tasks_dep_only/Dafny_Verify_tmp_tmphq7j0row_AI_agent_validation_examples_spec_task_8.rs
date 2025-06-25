// ATOM 
pub fn Power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Power(n - 1) }
}

pub fn Max(a: &[nat]) -> i32
    ensures(forall|i: usize| i < a.len() ==> a[i] <= result)
    ensures((result == 0 && a.len() == 0) || exists|i: usize| i < a.len() && result == a[i])
{
}

pub fn Cube(n: nat) -> nat
    ensures(result == n * n * n)
{
}

pub fn IncrementMatrix(a: &mut [[i32]])
    ensures(forall|i: usize, j: usize| i < a.len() && j < a[i].len() ==> a[i][j] == old(a)[i][j] + 1)
{
}

pub fn CopyMatrix(src: &[[i32]], dst: &mut [[i32]])
    requires(src.len() == dst.len() && forall|i: usize| i < src.len() ==> src[i].len() == dst[i].len())
    ensures(forall|i: usize, j: usize| i < src.len() && j < src[i].len() ==> dst[i][j] == old(src)[i][j])
{
}

pub fn DoubleArray(src: &[i32], dst: &mut [i32])
    requires(src.len() == dst.len())
    ensures(forall|i: usize| i < src.len() ==> dst[i] == 2 * old(src)[i])
{
}

pub fn RotateLeft(a: &mut [i32])
    requires(a.len() > 0)
    ensures(forall|i: usize| i < a.len() - 1 ==> a[i] == old(a)[i + 1])
    ensures(a[a.len() - 1] == old(a)[0])
{
}

pub fn RotateRight(a: &mut [i32])
    requires(a.len() > 0)
    ensures(forall|i: usize| 1 <= i && i < a.len() ==> a[i] == old(a)[i - 1])
    ensures(a[0] == old(a)[a.len() - 1])
{
}