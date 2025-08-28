use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        sum(v, i, (j - 1) as int) + v[(j - 1) as int] as int
    }
}

spec fn sum_max_to_right(v: Seq<i32>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}



spec fn sum2(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        v[i] as int + sum2(v, i + 1, j)
    }
}

//Now do the same but with a loop from right to left
spec fn sum_max_to_right2(v: Seq<i32>, j: int, i: int, s: int) -> bool //maximum sum stuck to the right
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
proof fn sum2_equiv_sum(v: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i == j {
    } else {
        sum2_equiv_sum(v, i + 1, j);
        assert(sum(v, i, j) == v[i] as int + sum(v, i + 1, j));
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn seg_suma_maxima2(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        0 <= result.1 <= i && 
        result.0 as int == sum2(v@, result.1 as int, (i + 1) as int) && 
        sum_max_to_right2(v@, 0, i as int, result.0 as int)
//Implement and verify
// </vc-spec>
// </vc-spec>

// <vc-code>
fn seg_suma_maxima2(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        0 <= result.1 <= i && 
        result.0 as int == sum2(v@, result.1 as int, (i + 1) as int) && 
        sum_max_to_right2(v@, 0, i as int, result.0 as int)
{
    let mut max_sum: i32 = v[i];
    let mut max_start: usize = i;
    let mut current_sum: i32 = v[i];
    let mut current_start: usize = i;

    let mut k: usize = i;
    while k > 0
        invariant
            0 <= k <= i,
            0 <= max_start <= i,
            0 <= current_start <= i,
            current_sum as int == sum2(v@, current_start as int, (i + 1) as int),
            max_sum as int == sum2(v@, max_start as int, (i + 1) as int),
            sum_max_to_right2(v@, k as int, i as int, max_sum as int)
        decreases k
    {
        k = k - 1;
        current_sum = current_sum + v[k];
        current_start = k;
        if current_sum > max_sum {
            max_sum = current_sum;
            max_start = current_start;
        }
    }

    (max_sum, max_start)
}
// </vc-code>

fn main() {}

}