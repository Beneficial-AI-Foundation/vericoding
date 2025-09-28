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
// No helpers needed for this proof.
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
    let mut k: int = i as int;
    let mut suffix_sum_i32: i32 = 0;
    let mut best_sum_i32: i32 = v[i];
    let mut best_idx: int = i as int;

    while (k >= 0)
        invariant { -1 <= k && k <= i as int }
        invariant { 0 <= best_idx && best_idx <= i as int }
        invariant { (best_sum_i32 as int) == sum2(v@, best_idx, (i as int) + 1) }
        invariant { (suffix_sum_i32 as int) == sum2(v@, k + 1, (i as int) + 1) }
        invariant { forall|l: int| k + 1 <= l && l <= i as int ==> #[trigger] sum2(v@, l, (i as int) + 1) <= (best_sum_i32 as int) }
        decreases (k + 1)
    {
        let s_i32: i32 = suffix_sum_i32 + v[k as usize];
        // relate s_i32 to sum2
        assert((suffix_sum_i32 as int) == sum2(v@, k + 1, (i as int) + 1));
        assert((v[k as usize] as int) + (suffix_sum_i32 as int) == (s_i32 as int));
        assert(sum2(v@, k, (i as int) + 1) == (v[k as usize] as int) + sum2(v@, k + 1, (i as int) + 1));
        assert((s_i32 as int) == sum2(v@, k, (i as int) + 1));

        suffix_sum_i32 = s_i32;
        if s_i32 > best_sum_i32 {
            best_sum_i32 = s_i32;
            best_idx = k;
        }
        k = k - 1;
    }

    assert(0 <= best_idx);
    (best_sum_i32, best_idx as usize)
}
// </vc-code>

fn main() {}

}