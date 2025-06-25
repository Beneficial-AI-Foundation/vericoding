use vstd::prelude::*;

verus! {

// 1 a)
// [ai, aj[
// ATOM 
spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j { 0 } else { a[j as usize - 1] + sum(a, i, j - 1) }
}

// 1 b)
// SPEC 
pub fn query(a: &[int], i: usize, j: usize) -> (res: int)
    requires(0 <= i <= j <= a.len())
    ensures(res == sum(a, i as int, j as int))
{
}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
// SPEC 
pub fn query2(a: &[int], i: usize, j: usize) -> (res: int)
    requires(0 <= i <= j <= a.len())
    ensures(res == sum(a, i as int, j as int))
{
}

}