use vstd::prelude::*;

verus! {

spec fn Sum2(v: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
{
    if i == j {
        0
    } else {
        v[i as usize] + Sum2(v, i + 1, j)
    }
}

spec fn SumMaxToRight2(v: &[int], j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> Sum2(v, l, ss) <= s
}

pub fn segSumaMaxima2(v: &[int], i: usize) -> (s: int, k: usize)
    requires(
        v.len() > 0 && i < v.len()
    )
    ensures(|result: (int, usize)|
        0 <= result.1 <= i && 
        result.0 == Sum2(v, result.1 as int, i as int + 1) && 
        SumMaxToRight2(v, 0, i as int, result.0)
    )
{
    
}

}