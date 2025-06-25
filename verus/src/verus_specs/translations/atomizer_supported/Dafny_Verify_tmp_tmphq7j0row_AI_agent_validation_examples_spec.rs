use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

pub fn compute_power(N: i32) -> (y: u32)
    requires(N >= 0)
    ensures(y == power(N as nat))
{
    unimplemented!()
}

pub fn max(a: &[u32]) -> (m: i32)
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i] <= m)
    ensures((m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i])
{
    unimplemented!()
}

pub fn cube(n: u32) -> (c: u32)
    ensures(c == n * n * n)
{
    unimplemented!()
}

pub fn increment_matrix(a: &mut Vec<Vec<i32>>)
    ensures(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i as int].len() ==> 
            a[i][j] == old(a)[i][j] + 1)
{
    unimplemented!()
}

pub fn copy_matrix(src: &Vec<Vec<i32>>, dst: &mut Vec<Vec<i32>>)
    requires(src.len() == dst.len() && 
             forall|i: int| 0 <= i < src.len() ==> src[i as int].len() == dst[i as int].len())
    ensures(forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[i as int].len() ==> 
            dst[i][j] == old(src)[i][j])
{
    unimplemented!()
}

pub fn double_array(src: &[i32], dst: &mut [i32])
    requires(src.len() == dst.len())
    ensures(forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * old(src)[i])
{
    unimplemented!()
}

pub fn rotate_left<T>(a: &mut [T])
    requires(a.len() > 0)
    ensures(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] == old(a)[(i + 1) as int])
    ensures(a[a.len() - 1] == old(a)[0])
{
    unimplemented!()
}

pub fn rotate_right<T>(a: &mut [T])
    requires(a.len() > 0)
    ensures(forall|i: int| 1 <= i < a.len() ==> a[i] == old(a)[(i - 1) as int])
    ensures(a[0] == old(a)[a.len() - 1])
{
    unimplemented!()
}

}