use vstd::prelude::*;

verus! {

spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j { 0 } else { a[i as usize] + sum(a, i+1, j) }
}

pub fn query(a: &[int], i: int, j: int) -> (res: int)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i, j)
{
}

spec fn is_prefix_sum_for(a: &[int], c: &[int]) -> bool
{
    a.len() + 1 == c.len() && c[0] == 0 &&
    forall|i: int| 0 <= i < a.len() ==> c[(i+1) as usize] == c[i as usize] + a[i as usize]
}

proof fn aux(a: &[int], c: &[int], i: int, j: int)
    requires 0 <= i <= j <= a.len()
    requires a.len() + 1 == c.len()
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures forall|k: int| i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k as usize] - c[i as usize] + c[j as usize] - c[k as usize]
{
}

pub fn queryFast(a: &[int], c: &[int], i: int, j: int) -> (r: int)
    requires a.len() + 1 == c.len() && c[0] == 0
    requires 0 <= i <= j <= a.len()
    requires is_prefix_sum_for(a, c)
    ensures r == sum(a, i, j)
{
}

pub fn Main()
{
}

}