// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_sum(xs: &Vec<i32>, start: int, len: int) -> int 
    decreases len
{
    if len <= 0 {
        0
    } else {
        xs[start] + spec_sum(xs, start + 1, len - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec_sum_zero proves spec_sum(...,0) == 0 */
proof fn spec_sum_zero(xs: &Vec<i32>, start: int) requires 0 <= start && start <= xs.len() as int ensures spec_sum(xs, start, 0) == 0 {
    assert(spec_sum(xs, start, 0) == 0);
}

/* helper modified by LLM (iteration 5): spec_sum_extend proves extension property of spec_sum */
proof fn spec_sum_extend(xs: &Vec<i32>, start: int, len: int) requires 0 <= start && 0 <= len && start + len + 1 <= xs.len() as int ensures spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs@[start + len] decreases len {
    if len == 0 {
        assert(spec_sum(xs, start, 1) == xs@[start] + spec_sum(xs, start + 1, 0));
        assert(spec_sum(xs, start, 0) == 0);
        assert(spec_sum(xs, start, 1) == spec_sum(xs, start, 0) + xs@[start + 0]);
    } else {
        spec_sum_extend(xs, start + 1, len - 1);
        assert(spec_sum(xs, start + 1, len) == spec_sum(xs, start + 1, len - 1) + xs@[start + len]);
        assert(spec_sum(xs, start, len + 1) == xs@[start] + spec_sum(xs, start + 1, len));
        assert(spec_sum(xs, start, len) == xs@[start] + spec_sum(xs, start + 1, len - 1));
        assert(spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs@[start + len]);
    }
}

// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(xs: &Vec<i32>) -> (result: i32)
    ensures
        xs.len() == 0 ==> result == 0,
        xs.len() > 0 ==> (
            exists|start: int, len: int| 
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                result == spec_sum(xs, start, len) as i32
        ) &&
        (forall|start: int, len: int|
            0 <= start < xs.len() && 
            1 <= len <= xs.len() - start
            ==> spec_sum(xs, start, len) <= result as int
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): brute-force max subarray with proofs */
{
    if xs.len() == 0 {
        return 0;
    }

    let n: int = xs.len() as int;
    let mut best_i: int = xs@[0] as int;
    let mut best_start: int = 0;
    let mut best_len: int = 1;

    let mut start: int = 0;
    while start < n
        invariant 0 <= start && start <= n
        invariant (forall |s: int, l: int| 0 <= s && s < start && 1 <= l && l <= n - s ==> spec_sum(xs, s, l) <= best_i)
        invariant (start == 0 || exists |s0: int, l0: int| 0 <= s0 && s0 < start && 1 <= l0 && l0 <= n - s0 && best_i == spec_sum(xs, s0, l0))
    {
        let mut j: int = start;
        let mut sum_i: int = 0;
        while j < n
            invariant start <= j && j <= n
            invariant sum_i == spec_sum(xs, start, j - start)
            invariant (forall |s: int, l: int| 0 <= s && s < start && 1 <= l && l <= n - s ==> spec_sum(xs, s, l) <= best_i)
            invariant (start == 0 || exists |s0: int, l0: int| 0 <= s0 && s0 < start && 1 <= l0 && l0 <= n - s0 && best_i == spec_sum(xs, s0, l0))
        {
            let old_j: int = j;
            let old_sum: int = sum_i;
            // add next element
            sum_i = sum_i + (xs@[j] as int);

            let cur_len: int = old_j - start + 1;
            if sum_i > best_i {
                best_i = sum_i;
                best_start = start;
                best_len = cur_len;
            }

            j = j + 1;

            proof {
                // old_sum == spec_sum(xs, start, old_j - start)
                assert(old_sum == spec_sum(xs, start, (old_j - start)));
                // extend by one element
                spec_sum_extend(xs, start, (old_j - start));
                assert(spec_sum(xs, start, (old_j - start) + 1) == spec_sum(xs, start, (old_j - start)) + xs@[old_j]);
                assert(spec_sum(xs, start, (j - start)) == spec_sum(xs, start, (old_j - start) + 1));
                assert(old_sum + xs@[old_j] == spec_sum(xs, start, (j - start)));
                assert(sum_i == spec_sum(xs, start, (j - start)));
            }
        }

        start = start + 1;

        proof {
            // when advancing start, best_i still represents max over seen subarrays
        }
    }

    // At this point best_i corresponds to some valid subarray; return it as i32
    best_i as i32
}

// </vc-code>

}
fn main() {}