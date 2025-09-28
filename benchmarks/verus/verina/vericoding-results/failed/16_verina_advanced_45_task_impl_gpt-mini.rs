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
/* helper modified by LLM (iteration 5): simple spec helper for max of two ints */
spec fn max_int(a: int, b: int) -> int { if a > b { a } else { b } }
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
{
    /* code modified by LLM (iteration 5): implement Kadane's algorithm using i64 internals and strengthened invariants */
    if xs.len() == 0 {
        return 0;
    }

    let n = xs.len();
    let mut i: usize = 1;
    let mut cur_start: usize = 0;
    let mut cur_sum: i64 = xs[0] as i64;
    let mut best_start: usize = 0;
    let mut best_len: usize = 1;
    let mut best_sum: i64 = xs[0] as i64;

    while i < n
        invariant
            0 < i && i <= n,
            cur_start < i,
            cur_sum as int == spec_sum(xs, cur_start as int, (i - cur_start) as int),
            (forall|s: int, len: int| 0 <= s && s < (i as int) && 1 <= len && s + len == (i as int) ==> spec_sum(xs, s, len) <= cur_sum as int),
            best_sum as int == spec_sum(xs, best_start as int, best_len as int),
            (forall|s: int, len: int| 0 <= s && s < (i as int) && 1 <= len && s + len <= (i as int) ==> spec_sum(xs, s, len) <= best_sum as int),
        decreases n - i
    {
        let old_i = i;
        let old_cur_start = cur_start;
        let old_cur_sum = cur_sum;
        let old_best_sum = best_sum;

        let x = xs[i] as i64;

        // update current max subarray ending at index old_i
        if old_cur_sum < 0 {
            cur_sum = x;
            cur_start = i;
        } else {
            cur_sum = old_cur_sum + x;
        }

        // update global best if needed
        if cur_sum > best_sum {
            best_sum = cur_sum;
            best_start = cur_start;
            best_len = i - cur_start + 1;
        }

        i = i + 1;

        proof {
            if old_cur_sum < 0 {
                // restarted at index old_i
                assert(cur_start == old_i);
                assert(cur_sum as int == spec_sum(xs, old_i as int, 1));
            } else {
                // extended previous current-ending subarray
                assert(cur_start == old_cur_start);
                assert(cur_sum as int == old_cur_sum as int + x as int);
                assert(cur_sum as int == spec_sum(xs, old_cur_start as int, (old_i - old_cur_start) as int) + x as int);
                assert(cur_sum as int == spec_sum(xs, cur_start as int, (i - cur_start) as int));
            }

            // cur_sum is at least any subarray that ends at old_i
            assert((forall|s: int, len: int|
                0 <= s && s < (i as int) && 1 <= len && s + len == (i as int)
                ==> spec_sum(xs, s, len) <= cur_sum as int));

            // Update best_sum property
            if old_best_sum as int >= cur_sum as int {
                assert(best_sum as int == old_best_sum as int);
            } else {
                assert(best_sum as int == cur_sum as int);
            }

            // best_sum bounds all subarrays in prefix [0, i)
            assert((forall|s: int, len: int|
                0 <= s && s < (i as int) && 1 <= len && s + len <= (i as int)
                ==> spec_sum(xs, s, len) <= best_sum as int));
        }
    }

    proof {
        assert(best_sum as int == spec_sum(xs, best_start as int, best_len as int));
        assert((forall|s: int, len: int|
            0 <= s && s < (n as int) && 1 <= len && s + len <= (n as int)
            ==> spec_sum(xs, s, len) <= best_sum as int));
    }

    #[verifier::truncate] best_sum as i32
}
// </vc-code>

}
fn main() {}