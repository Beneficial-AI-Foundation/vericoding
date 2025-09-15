// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use Seq<i64> and return i64 for sums */
spec fn sub_sum(seq: Seq<i64>, start: nat, end: nat) -> i64
    requires start <= end && end <= seq.len()
{
    if start == end { 0 } else { seq.index(start) + sub_sum(seq, start + 1, end) }
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(numbers: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i64 for runtime sums and cast vector elements to i64 */
    let n = numbers.len();
    let mut best: i64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant 0 <= best,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j <= n
            invariant 0 <= best,
            decreases n + 1 - j
        {
            let mut k: usize = i;
            let mut sum: i64 = 0;
            while k < j
                invariant i <= k && k <= j,
                          sum == sub_sum(numbers@.map(|x: i32| x as i64), i as nat, k as nat),
                decreases j - k
            {
                let old_k = k;
                let old_sum = sum;
                let v = numbers[old_k] as i64;
                sum = old_sum + v;
                k = old_k + 1;
                proof {
                    assert(old_sum == sub_sum(numbers@.map(|x: i32| x as i64), i as nat, old_k as nat));
                    assert(sum == old_sum + v);
                    assert(sum == sub_sum(numbers@.map(|x: i32| x as i64), i as nat, (old_k + 1) as nat));
                }
            }
            if sum > best {
                best = sum;
            } else {
                ()
            }
            j = j + 1;
        }
        i = i + 1;
    }
    best as i32
}
// </vc-code>

}
fn main() {}