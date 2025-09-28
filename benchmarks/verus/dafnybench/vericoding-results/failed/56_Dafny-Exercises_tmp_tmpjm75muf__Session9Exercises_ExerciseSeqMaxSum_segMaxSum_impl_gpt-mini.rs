use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        sum(v, i, (j-1) as int) + v[(j-1) as int]
    }
}

spec fn sum_max_to_right(v: Seq<int>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}

spec fn sum2(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        v[i as int] + sum2(v, (i+1) as int, j)
    }
}

spec fn sum_max_to_right2(v: Seq<int>, j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
proof fn sum_split_left(seq: Seq<int>, l: int, ss: int)
    requires 0 <= l && l + 1 <= ss && ss <= seq.len()
    decreases ss - l
{
    if l + 1 == ss {
        // sum(seq, l, l+1) == seq[l]
        assert(sum(seq, l, ss) == seq@[l]);
    } else {
        // ss > l+1
        sum_split_left(seq, l, ss - 1);
        // sum(seq, l, ss-1) == seq@[l] + sum(seq, l+1, ss-1)
        assert(sum(seq, l, ss - 1) == seq@[l] + sum(seq, l + 1, ss - 1));
        // sum(seq, l, ss) == sum(seq, l, ss-1) + seq@[ss-1]
        assert(sum(seq, l, ss) == sum(seq, l, ss - 1) + seq@[ss - 1]);
        // combine
        assert(sum(seq, l, ss) == seq@[l] + sum(seq, l + 1, ss));
    }
}
// </vc-helpers>

// <vc-spec>
fn seg_max_sum(v: &[i32], i: usize) -> (i32, usize)
    requires v.len() > 0 && i < v.len()
    ensures |result: (i32, usize)|
        result.1 <= i && 
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int) &&
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
// </vc-spec>
// <vc-code>
{
    let seq = v@.map_values(|x: i32| x as int);
    let mut best_idx: usize = i;
    let mut best_sum: i32 = v[i];
    let mut cur_sum: i32 = v[i];
    let mut k: usize = i;

    while k > 0
        invariant k <= i;
        invariant (cur_sum as int) == sum(seq, k as int, (i as int) + 1);
        invariant (best_sum as int) == sum(seq, best_idx as int, (i as int) + 1);
        invariant best_idx <= i;
        invariant forall |l: int| (k as int) <= l && l <= i as int ==>
            #[trigger] sum(seq, l, (i as int) + 1) <= (best_sum as int);
        decreases k;
    {
        let k1: usize = k - 1;
        let inc: i32 = v[k1];
        let new_sum: i32 = cur_sum + inc;

        // show new_sum as int == sum(seq, k1, i+1)
        sum_split_left(seq, k1 as int, (i as int) + 1);
        assert(sum(seq, k1 as int, (i as int) + 1) == seq@[k1 as int] + sum(seq, (k1 as int) + 1, (i as int) + 1));
        assert((k as int) == (k1 as int) + 1);
        assert(sum(seq, (k1 as int) + 1, (i as int) + 1) == (cur_sum as int));
        assert(seq@[k1 as int] == (inc as int));
        assert(sum(seq, k1 as int, (i as int) + 1) == (inc as int) + (cur_sum as int));
        assert((new_sum as int) == sum(seq, k1 as int, (i as int) + 1));

        cur_sum = new_sum;
        if cur_sum > best_sum {
            best_sum = cur_sum;
            best_idx = k1 as usize;
        }

        k = k1;
    }

    (best_sum, best_idx)
}
// </vc-code>

fn main() {
}

}