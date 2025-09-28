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
proof fn sum2_unfold(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j <= v.len()
    ensures
        sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j)
{
    // By definition of sum2:
    assert(sum2(v, i, j) == if i == j { 0 } else { v[i] as int + sum2(v, i + 1, j) });
    assert(i < j);
}

proof fn sum2_base(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len()
    ensures
        sum2(v, i, i + 1) == v[i] as int
{
    sum2_unfold(v, i, i + 1);
    assert(sum2(v, i + 1, i + 1) == 0);
}

proof fn sum2_shift_left(v: Seq<i32>, l: int, j: int)
    requires
        0 <= l < j <= v.len()
    ensures
        sum2(v, l, j) == v[l] as int + sum2(v, l + 1, j)
{
    sum2_unfold(v, l, j);
}
// </vc-helpers>

// <vc-spec>
fn seg_suma_maxima2(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        0 <= result.1 <= i && 
        result.0 as int == sum2(v@, result.1 as int, (i + 1) as int) && 
        sum_max_to_right2(v@, 0, i as int, result.0 as int)
//Implement and verify
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let mut k: usize = i;
    let mut running: i32 = v[i];
    let mut best_sum: i32 = running;
    let mut best_l: usize = i;

    proof {
        assert(0 <= i as int && i as int < v@.len());
        sum2_base(v@, i as int);
        assert(running as int == sum2(v@, i as int, (i + 1) as int));
        assert(best_sum as int == sum2(v@, best_l as int, (i + 1) as int));
// </vc-code>

fn main() {}

}