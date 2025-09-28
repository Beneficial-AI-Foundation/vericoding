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
proof fn sum2_split(v: Seq<i32>, i: int, k: int, j: int)
    requires 0 <= i <= k <= j <= v.len()
    ensures sum2(v, i, j) == sum2(v, i, k) + sum2(v, k, j)
{
    if i == k {
        assert(sum2(v, i, j) == sum2(v, k, j));
        assert(sum2(v, i, k) == 0);
    } else if k == j {
        assert(sum2(v, i, j) == sum2(v, i, k));
        assert(sum2(v, k, j) == 0);
    } else {
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_split(v, i + 1, k, j);
    }
}

proof fn sum2_monotonic(v: Seq<i32>, i: int, j: int, k: int)
    requires 0 <= i <= j < k <= v.len()
    recommends j == k - 1
    ensures sum2(v, i, k) == sum2(v, i, j) + v[j] as int
{
    if i == j {
        assert(sum2(v, i, j) == 0);
        assert(sum2(v, i, k) == v[j] as int);
    } else {
        assert(sum2(v, i, k) == v[i] as int + sum2(v, i + 1, k));
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_monotonic(v, i + 1, j, k);
    }
}

proof fn lemma_sum2_range(v: Seq<i32>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum2(v, i, k) == sum2(v, i, j) + sum2(v, j,
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
proof fn sum2_split(v: Seq<i32>, i: int, k: int, j: int)
    requires 0 <= i <= k <= j <= v.len()
    ensures sum2(v, i, j) == sum2(v, i, k) + sum2(v, k, j)
{
    if i == k {
        assert(sum2(v, i, j) == sum2(v, k, j));
        assert(sum2(v, i, k) == 0);
    } else if k == j {
        assert(sum2(v, i, j) == sum2(v, i, k));
        assert(sum2(v, k, j) == 0);
    } else {
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_split(v, i + 1, k, j);
    }
}

proof fn sum2_monotonic(v: Seq<i32>, i: int, j: int, k: int)
    requires 0 <= i <= j < k <= v.len()
    recommends j == k - 1
    ensures sum2(v, i, k) == sum2(v, i, j) + v[j] as int
{
    if i == j {
        assert(sum2(v, i, j) == 0);
        assert(sum2(v, i, k) == v[j] as int);
    } else {
        assert(sum2(v, i, k) == v[i] as int + sum2(v, i + 1, k));
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_monotonic(v, i + 1, j, k);
    }
}

proof fn lemma_sum2_range(v: Seq<i32>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum2(v, i, k) == sum2(v, i, j) + sum2(v, j,
// </vc-code>

fn main() {}

}