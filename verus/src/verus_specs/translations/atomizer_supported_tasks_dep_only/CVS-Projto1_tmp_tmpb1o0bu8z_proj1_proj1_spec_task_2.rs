use vstd::prelude::*;

verus! {

pub fn sum(a: &[int], i: int, j: int) -> int
    requires(
        0 <= i <= j <= a.len()
    )
{
    unimplemented!()
}

pub proof fn queryLemma(a: &[int], i: int, j: int, k: int)
    requires(
        0 <= i <= k <= j <= a.len()
    )
    ensures(
        sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
    )
{
}

pub fn queryFast(a: &[int], c: &[int], i: int, j: int) -> int
    requires(
        is_prefix_sum_for(a, c) && 0 <= i <= j <= a.len() < c.len()
    )
    ensures(|r: int|
        r == sum(a, i, j)
    )
{
    unimplemented!()
}

pub spec fn is_prefix_sum_for(a: &[int], c: &[int]) -> bool
{
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

}