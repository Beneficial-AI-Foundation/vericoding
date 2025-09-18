// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_subarray_sum(sequence: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end || start < 0 || end > sequence.len() {
        0
    } else if start + 1 == end {
        sequence[start] as int
    } else {
        sequence[start] as int + spec_subarray_sum(sequence, start + 1, end)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to show appending one element extends the spec sum appropriately */
fn lemma_spec_append(sequence: Seq<i32>, start: int, end: int)
    requires
        0 <= start, start < end,
        end < sequence.len() as int,
    ensures
        spec_subarray_sum(sequence, start, end+1) == spec_subarray_sum(sequence, start, end) + sequence[end] as int,
    decreases
        end - start,
{
    if start + 1 == end {
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int);
        assert(spec_subarray_sum(sequence, start, end+1) == sequence[start] as int + sequence[end] as int);
    } else {
        lemma_spec_append(sequence, start+1, end);
        assert(spec_subarray_sum(sequence, start+1, end+1) == spec_subarray_sum(sequence, start+1, end) + sequence[end] as int);
        assert(spec_subarray_sum(sequence, start, end+1) == sequence[start] as int + spec_subarray_sum(sequence, start+1, end+1));
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int + spec_subarray_sum(sequence, start+1, end));
        assert(spec_subarray_sum(sequence, start, end+1) == spec_subarray_sum(sequence, start, end) + sequence[end] as int);
    }
}

/* helper modified by LLM (iteration 5): lemma for single-element subarray equality */
fn lemma_spec_single(sequence: Seq<i32>, i: int)
    requires
        0 <= i, i < sequence.len() as int,
    ensures
        spec_subarray_sum(sequence, i, i+1) == sequence[i] as int,
{
    assert(spec_subarray_sum(sequence, i, i+1) == sequence[i] as int);
}

// </vc-helpers>

// <vc-spec>
fn task_code(sequence: Vec<i32>) -> (result: i32)
    requires sequence.len() > 0,
    ensures 
        exists|start: int, end: int| 
            0 <= start < end <= sequence.len() && 
            result as int == spec_subarray_sum(sequence@, start, end) &&
            forall|s: int, e: int| (0 <= s < e <= sequence.len()) ==> 
                spec_subarray_sum(sequence@, s, e) <= result as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Kadane's algorithm with corrected invariant cast parentheses and proofs */
    let n = sequence.len();
    let mut i: usize = 1;

    let mut cur_start_rt: usize = 0;
    let mut cur_sum_rt: i32 = sequence[0];
    let mut best_start_rt: usize = 0;
    let mut best_end_rt: usize = 1;
    let mut best_sum_rt: i32 = cur_sum_rt;

    proof {
        lemma_spec_single(sequence@, 0 as int);
        assert(cur_sum_rt as int == spec_subarray_sum(sequence@, cur_start_rt as int, 1));
        assert(best_sum_rt as int == spec_subarray_sum(sequence@, best_start_rt as int, best_end_rt as int));
        assert(forall(|s: int, e: int| 0 <= s < e && e <= 1 ==> spec_subarray_sum(sequence@, s, e) <= best_sum_rt as int));
    }

    while i < n
        invariant
            i <= n,
            0 <= (cur_start_rt as int), (cur_start_rt as int) < (i as int),
            0 < (best_end_rt as int), (best_end_rt as int) <= (i as int),
            (cur_sum_rt as int) == spec_subarray_sum(sequence@, (cur_start_rt as int), (i as int)),
            forall|s: int| 0 <= s < (i as int) ==> spec_subarray_sum(sequence@, s, (i as int)) <= (cur_sum_rt as int),
            (best_sum_rt as int) == spec_subarray_sum(sequence@, (best_start_rt as int), (best_end_rt as int)),
            forall|s: int, e: int| 0 <= s < e && e <= (i as int) ==> spec_subarray_sum(sequence@, s, e) <= (best_sum_rt as int),
        decreases
            n - i
    {
        let x: i32 = sequence[i];

        if cur_sum_rt + x >= x {
            let old_cur_sum = cur_sum_rt;
            cur_sum_rt = cur_sum_rt + x;
            proof {
                lemma_spec_append(sequence@, cur_start_rt as int, i as int);
                assert(spec_subarray_sum(sequence@, cur_start_rt as int, (i as int) + 1) == old_cur_sum as int + x as int);
                assert(cur_sum_rt as int == spec_subarray_sum(sequence@, cur_start_rt as int, (i as int) + 1));
                assert(forall(|s: int| 0 <= s < (i as int) ==> spec_subarray_sum(sequence@, s, (i as int) + 1) <= cur_sum_rt as int));
                lemma_spec_single(sequence@, i as int);
                assert(spec_subarray_sum(sequence@, i as int, (i as int) + 1) == x as int);
            }
        } else {
            cur_sum_rt = x;
            cur_start_rt = i;
            proof {
                lemma_spec_single(sequence@, i as int);
                assert(cur_sum_rt as int == spec_subarray_sum(sequence@, cur_start_rt as int, (i as int) + 1));
                assert(forall(|s: int| 0 <= s < (i as int) ==> spec_subarray_sum(sequence@, s, (i as int) + 1) <= cur_sum_rt as int));
            }
        }

        if cur_sum_rt > best_sum_rt {
            best_sum_rt = cur_sum_rt;
            best_start_rt = cur_start_rt;
            best_end_rt = i + 1;
            proof {
                assert(best_sum_rt as int == spec_subarray_sum(sequence@, best_start_rt as int, best_end_rt as int));
                assert(forall(|s: int, e: int| 0 <= s < e && e <= (i as int) + 1 ==> spec_subarray_sum(sequence@, s, e) <= best_sum_rt as int));
            }
        } else {
            proof {
                assert(forall(|s: int, e: int| 0 <= s < e && e <= (i as int) + 1 ==> spec_subarray_sum(sequence@, s, e) <= best_sum_rt as int));
            }
        }

        i = i + 1;
    }

    (best_sum_rt)
}

// </vc-code>

}
fn main() {}