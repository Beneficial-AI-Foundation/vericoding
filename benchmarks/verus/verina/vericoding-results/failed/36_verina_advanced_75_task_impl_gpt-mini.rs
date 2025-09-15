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
proof fn spec_subarray_sum_singleton(sequence: Seq<i32>, idx: int)
    requires 0 <= idx < sequence.len()
    ensures spec_subarray_sum(sequence, idx, idx + 1) == sequence@[idx] as int
{
}

proof fn spec_subarray_sum_extend(sequence: Seq<i32>, start: int, mid: int)
    requires 0 <= start <= mid < sequence.len()
    ensures spec_subarray_sum(sequence, start, mid + 1) == spec_subarray_sum(sequence, start, mid) + sequence@[mid] as int
    decreases mid - start
{
    if start < mid {
        proof {
            spec_subarray_sum_extend(sequence, start + 1, mid);
        }
    } else {
        // start == mid, follows directly from the definition of spec_subarray_sum
    }
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
    let n: int = sequence.len();

    // Initialize best to the first non-empty subarray [0,1)
    let mut best_start: int = 0;
    let mut best_end: int = 1;
    let mut best_sum: i32 = sequence.get(0usize);

    proof {
        spec_subarray_sum_singleton(sequence@, 0);
    }

    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n,
        invariant 0 <= best_start < best_end <= n,
        invariant best_sum as int == spec_subarray_sum(sequence@, best_start, best_end),
        invariant forall |s: int, e: int| 0 <= s < e <= n && s < i ==> spec_subarray_sum(sequence@, s, e) <= best_sum as int,
        decreases n - i
    {
        let mut j: int = i;
        let mut cur_sum: i32 = 0; // corresponds to spec_subarray_sum(sequence@, i, j)

        while j < n
            invariant i <= j <= n,
            invariant cur_sum as int == spec_subarray_sum(sequence@, i, j),
            invariant 0 <= best_start < best_end <= n,
            invariant best_sum as int == spec_subarray_sum(sequence@, best_start, best_end),
            invariant forall |s: int, e: int| 0 <= s < e <= n && (s < i || (s == i && e <= j)) ==> spec_subarray_sum(sequence@, s, e) <= best_sum as int,
            decreases n - j
        {
            // Extend current subarray [i, j) by element at j to get [i, j+1)
            let vj: i32 = sequence.get(j as usize);
            cur_sum = cur_sum + vj;
            j = j + 1;

            proof {
                // By lemma: spec_subarray_sum(sequence, i, j) == spec_subarray_sum(sequence, i, j-1) + sequence@[j-1]
                spec_subarray_sum_extend(sequence@, i, j - 1);
            }

            if cur_sum > best_sum {
                best_sum = cur_sum;
                best_start = i;
                best_end = j;
                // best_sum corresponds to spec_subarray_sum(sequence@, best_start, best_end) by the inner invariant
            }
        }

        i = i + 1;
    }

    // At the end, best_sum is the maximum over all non-empty subarrays
    result: i32 = best_sum;
    result
}
// </vc-code>

}
fn main() {}