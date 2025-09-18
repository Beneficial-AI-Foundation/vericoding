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
/* helper modified by LLM (iteration 5): adjust precondition to compare with xs.len() as int and keep recursive proof */
proof fn spec_sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len < xs.len() as int,
    ensures
        spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len],
    decreases len
{
    if len == 0 {
        assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
        assert(spec_sum(xs, start, 0) == 0);
        assert(spec_sum(xs, start, 1) == spec_sum(xs, start, 0) + xs[start]);
    } else {
        spec_sum_extend(xs, start + 1, len - 1);
        assert(spec_sum(xs, start, len + 1) == xs[start] + spec_sum(xs, start + 1, len));
        assert(spec_sum(xs, start, len) == xs[start] + spec_sum(xs, start + 1, len - 1));
        assert(spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len]);
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
/* code modified by LLM (iteration 5): brute-force nested loops with tracked specs and safe i128 runtime accumulators */
{
    let n: usize = xs.len();
    if n == 0 {
        0
    } else {
        // runtime accumulators use i128 to avoid overflow warnings
        let mut best_sum_r: i128 = xs[0usize] as i128;
        let mut best_start_r: usize = 0usize;
        let mut best_len_r: usize = 1usize;

        let tracked mut best_sum: int = best_sum_r as int;
        let tracked mut best_start: int = best_start_r as int;
        let tracked mut best_len: int = best_len_r as int;
        let tracked n_int: int = n as int;

        let mut start_usize: usize = 0usize;
        let tracked mut start: int = 0;
        while start_usize < n
            invariant
                0 <= start_usize && start_usize <= n,
                0 <= best_start,
                1 <= best_len,
                best_sum == spec_sum(xs, best_start, best_len),
                (forall|s: int, l: int| 0 <= s && 1 <= l && s + l <= start ==> spec_sum(xs, s, l) <= best_sum),
            decreases n_int - start
        {
            proof {
                start = start_usize as int;
            }

            let mut curr_sum_r: i128 = 0i128;
            let tracked mut curr_sum: int = 0;
            let mut len_usize: usize = 0usize;
            while len_usize < n - start_usize
                invariant
                    len_usize <= n - start_usize,
                    curr_sum == spec_sum(xs, start, len_usize as int),
                decreases (n_int - start) - (len_usize as int)
            {
                let idx = start_usize + len_usize;
                assert(idx < xs.len());
                let x = xs[idx];
                curr_sum_r = curr_sum_r + (x as i128);
                proof {
                    curr_sum = curr_sum + (x as int);
                    spec_sum_extend(xs, start, len_usize as int);
                }
                len_usize = len_usize + 1;
                if curr_sum_r > best_sum_r {
                    best_sum_r = curr_sum_r;
                    best_start_r = start_usize;
                    best_len_r = len_usize;
                    proof {
                        best_sum = best_sum_r as int;
                        best_start = best_start_r as int;
                        best_len = best_len_r as int;
                    }
                }
            }

            start_usize = start_usize + 1;
            proof {
                start = start + 1;
            }
        }

        // return truncated result to i32 (allowing cast truncation as needed)
        let result: i32 = #[verifier::truncate] best_sum as i32;
        result
    }
}

// </vc-code>

}
fn main() {}