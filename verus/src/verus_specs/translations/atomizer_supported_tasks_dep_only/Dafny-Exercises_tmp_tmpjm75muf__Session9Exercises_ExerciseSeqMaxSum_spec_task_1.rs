use vstd::prelude::*;

verus! {

spec fn Sum(v: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
{
    if i == j { 0 } else { Sum(v, i, j-1) + v[j-1] }
}

spec fn SumMaxToRight(v: &[int], i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i+1 ==> Sum(v, l, ss) <= s
}

pub fn segMaxSum(v: &[int], i: usize) -> (s: int, k: usize)
    requires(
        v.len() > 0 && i < v.len()
    )
    ensures(|result: (int, usize)| {
        let (s, k) = result;
        k <= i && s == Sum(v, k as int, i as int + 1) && SumMaxToRight(v, i as int, s)
    })
{
    todo!()
}

}