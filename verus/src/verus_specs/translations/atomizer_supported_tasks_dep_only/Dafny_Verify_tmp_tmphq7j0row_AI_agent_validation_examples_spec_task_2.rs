use vstd::prelude::*;

spec fn Power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

pub fn ComputePower1(N: int) -> (y: nat)
    requires(N >= 0)
    ensures(y == Power(N as nat))
{
}

pub fn Max(a: &[nat]) -> (m: int)
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i as usize] <= m)
    ensures((m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i as usize])
{
}

pub fn Cube(n: nat) -> (c: nat)
    ensures(c == n * n * n)
{
}

pub fn IncrementMatrix(a: &mut [[int]])
    ensures(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i as usize].len() ==> a[i as usize][j as usize] == old(a)[i as usize][j as usize] + 1)
{
}

pub fn CopyMatrix(src: &[[int]], dst: &mut [[int]])
    requires(src.len() == dst.len() && forall|i: int| 0 <= i < src.len() ==> src[i as usize].len() == dst[i as usize].len())
    ensures(forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[i as usize].len() ==> dst[i as usize][j as usize] == old(src)[i as usize][j as usize])
{
}

pub fn DoubleArray(src: &[int], dst: &mut [int])
    requires(src.len() == dst.len())
    ensures(forall|i: int| 0 <= i < src.len() ==> dst[i as usize] == 2 * old(src)[i as usize])
{
}

pub fn RotateLeft<T>(a: &mut [T])
    requires(a.len() > 0)
    ensures(forall|i: int| 0 <= i < a.len() - 1 ==> a[i as usize] == old(a)[(i + 1) as usize])
    ensures(a[(a.len() - 1) as usize] == old(a)[0])
{
}

pub fn RotateRight<T>(a: &mut [T])
    requires(a.len() > 0)
    ensures(forall|i: int| 1 <= i < a.len() ==> a[i as usize] == old(a)[(i - 1) as usize])
    ensures(a[0] == old(a)[(a.len() - 1) as usize])
{
}