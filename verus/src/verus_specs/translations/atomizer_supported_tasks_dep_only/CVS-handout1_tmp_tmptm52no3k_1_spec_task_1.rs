use vstd::prelude::*;

verus! {

spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j { 0 } else { a[i as usize] + sum(a, i + 1, j) }
}

pub fn query(a: &[int], i: int, j: int) -> (res: int)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i, j)
{
    unimplemented!()
}

}