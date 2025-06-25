use vstd::prelude::*;

verus! {

spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j { 0 } else { a[j as usize - 1] + sum(a, i, j - 1) }
}

pub fn queryFast(a: &[int], c: &[int], i: int, j: int) -> (r: int)
    requires(
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c)
    )
    ensures(r == sum(a, i, j))
{
    unimplemented!()
}

spec fn is_prefix_sum_for(a: &[int], c: &[int]) -> bool {
    a.len() + 1 == c.len() && forall|i: int| 0 <= i <= a.len() ==> c[i as usize] == sum(a, 0, i)
}

proof fn proof(a: &[int], i: int, j: int, k: int)
    requires(0 <= i <= k <= j <= a.len())
    ensures(sum(a, i, k) + sum(a, k, j) == sum(a, i, j))
{
    unimplemented!()
}

}