use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

pub fn max(a: &[nat]) -> (m: i32)
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= m,
        (m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i]
{
}

pub fn cube(n: nat) -> (c: nat)
    ensures c == n * n * n
{
}

pub fn increment_matrix(a: &mut Vec<Vec<i32>>)
    requires old(a).len() > 0 ==> old(a)[0].len() > 0,
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == old(a)[i].len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> a[i][j] == old(a)[i][j] + 1
{
}

pub fn copy_matrix(src: &Vec<Vec<i32>>, dst: &mut Vec<Vec<i32>>)
    requires 
        src.len() == dst.len(),
        forall|i: int| 0 <= i < src.len() ==> src[i].len() == dst[i].len()
    ensures forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[i].len() ==> dst[i][j] == old(src)[i][j]
{
}

pub fn double_array(src: &[i32], dst: &mut [i32])
    requires src.len() == dst.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * old(src)[i]
{
}

}