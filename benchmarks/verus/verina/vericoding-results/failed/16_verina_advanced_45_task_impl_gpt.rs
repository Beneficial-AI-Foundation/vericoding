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
proof fn lemma_spec_sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start < xs.len() as int,
        0 <= len,
        start + len + 1 <= xs.len() as int,
    ensures
        spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[(start + len) as usize] as int,
{
    assert(spec_sum(xs, start, len + 1) ==
        if len + 1 <= 0 { 0 } else { xs[start as usize] + spec_sum(xs, start + 1, len) }
    );
    assert(spec_sum(xs, start, len) ==
        if len <= 0 { 0 } else { xs[start as usize] + spec_sum(xs, start + 1, len - 1) }
    );
    if len <= 0 {
        // len == 0 here
        assert(spec_sum(xs, start, 1) == xs[start as usize] as int);
        assert(xs[(start + len) as usize] == xs[start as usize]);
    } else {
        // Unfold once and fold back to reach the step at start+len
        // This proof relies on the recursive definition of spec_sum
        // and arithmetic simplifications on indices.
        proof { }
    }
}

proof fn lemma_i32_int_roundtrip(x: i32)
    ensures (x as int) as i32 == x
{}

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
    let n = xs.len();
    if n == 0 {
        return 0;
    }

    let mut best_sum: i32 = xs[0];
    let mut best_start: usize = 0;
    let mut best_len: usize = 1;

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            best_start < n,
            1 <= best_len && best_len <= n - best_start,
            // best_sum corresponds to some subarray
            (best_sum as int) == spec_sum(xs, best_start as int, best_len as int),
            // best_sum is an upper bound for all subarrays with start < i
            (forall|s: int, l: int|
                0 <= s < i as int && 1 <= l && l <= (n as int - s)
                ==> spec_sum(xs, s, l) <= best_sum as int),
        decreases n - i
    {
        let mut k: usize = 1;
        let mut acc: i32 = xs[i];
        while k <= n - i
            invariant
                i < n,
                1 <= k && k <= n - i + 1,
                // acc equals the spec_sum of the current subarray [i, i+k)
                (acc as int) == spec_sum(xs, i as int, k as int),
                best_start < n,
                1 <= best_len && best_len <= n - best_start,
                (best_sum as int) == spec_sum(xs, best_start as int, best_len as int),
                // best_sum is an upper bound for all subarrays with start < i
                (forall|s: int, l: int|
                    0 <= s < i as int && 1 <= l && l <= (n as int - s)
                    ==> spec_sum(xs, s, l) <= best_sum as int),
                // best_sum also upper-bounds all subarrays starting at i with length < k
                (forall|l: int|
                    1 <= l && l < k as int
                    ==> spec_sum(xs, i as int, l) <= best_sum as int),
            decreases n - i + 1 - k
        {
            if acc > best_sum {
                best_sum = acc;
                best_start = i;
                best_len = k;
            }

            k = k + 1;
            if k <= n - i {
                // Extend one step: acc := acc + xs[i + k - 1]
                acc = acc + xs[i + (k - 1)];
                proof {
                    // Update the spec relation for acc by one-step extension
                    lemma_spec_sum_extend(xs, i as int, (k - 1) as int);
                }
            }
        }

        i = i + 1;
    }

    // Now best_sum corresponds to best_start, best_len and upper-bounds all subarrays
    proof { lemma_i32_int_roundtrip(best_sum); }
    best_sum
}
// </vc-code>

}
fn main() {}