use vstd::prelude::*;

spec fn Sum(v: &[i32], i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
{
    if i == j { 0 } else { Sum(v, i, j - 1) + v[j - 1] }
}

spec fn SumMaxToRight(v: &[i32], i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> Sum(v, l, ss) <= s
}

pub fn segMaxSum(v: &[i32], i: usize) -> (s: i32, k: usize)
    requires(
        v.len() > 0 && 0 <= i < v.len()
    )
    ensures(|result: (i32, usize)|
        0 <= result.1 <= i && result.0 == Sum(v, result.1 as int, i as int + 1) && SumMaxToRight(v, i as int, result.0)
    )
{
}

spec fn Sum2(v: &[i32], i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
{
    if i == j { 0 } else { v[i] + Sum2(v, i + 1, j) }
}

spec fn SumMaxToRight2(v: &[i32], j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> Sum2(v, l, ss) <= s
}

pub fn segSumaMaxima2(v: &[i32], i: usize) -> (s: i32, k: usize)
    requires(
        v.len() > 0 && 0 <= i < v.len()
    )
    ensures(|result: (i32, usize)|
        0 <= result.1 <= i && result.0 == Sum2(v, result.1 as int, i as int + 1) && SumMaxToRight2(v, 0, i as int, result.0)
    )
{
}