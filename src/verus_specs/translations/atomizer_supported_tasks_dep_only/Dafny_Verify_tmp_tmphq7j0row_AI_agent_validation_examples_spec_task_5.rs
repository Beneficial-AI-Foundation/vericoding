use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

pub fn compute_power1(N: int) -> (y: nat)
    requires(N >= 0)
    ensures(y == power(N as nat))
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

pub fn increment_matrix(a: &mut [[int]])
    ensures(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[0].len() ==> a[i][j] == old(a)[i][j] + 1)
{
}

pub fn copy_matrix(src: &[[int]], dst: &mut [[int]])
    requires(src.len() == dst.len() && src[0].len() == dst[0].len())
    ensures(forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[0].len() ==> dst[i][j] == old(src)[i][j])
{
}

}