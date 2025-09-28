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
/* helper modified by LLM (iteration 5): Fix postcondition proofs with explicit reasoning */
proof fn lemma_spec_sum_single(xs: &Vec<i32>, start: int)
    requires 0 <= start < xs.len()
    ensures spec_sum(xs, start, 1) == xs[start] as int
{
    // spec_sum(xs, start, 1) = xs[start] + spec_sum(xs, start + 1, 0) = xs[start] + 0 = xs[start]
    assert(spec_sum(xs, start + 1, 0) == 0);
}

proof fn lemma_spec_sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires 0 <= start < xs.len(), len > 0, start + len < xs.len()
    ensures spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len] as int
    decreases len
{
    if len == 1 {
        // spec_sum(xs, start, 2) = xs[start] + spec_sum(xs, start + 1, 1)
        // spec_sum(xs, start + 1, 1) = xs[start + 1] by definition
        // spec_sum(xs, start, 1) = xs[start] by definition
        assert(spec_sum(xs, start + 1, 1) == xs[start + 1] as int);
        assert(spec_sum(xs, start, 1) == xs[start] as int);
    } else {
        // spec_sum(xs, start, len + 1) = xs[start] + spec_sum(xs, start + 1, len)
        // By induction: spec_sum(xs, start + 1, len) = spec_sum(xs, start + 1, len - 1) + xs[start + len]
        lemma_spec_sum_extend(xs, start + 1, len - 1);
        assert(spec_sum(xs, start + 1, len) == spec_sum(xs, start + 1, len - 1) + xs[start + len] as int);
        assert(spec_sum(xs, start, len) == xs[start] as int + spec_sum(xs, start + 1, len - 1));
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
{
    /* code modified by LLM (iteration 5): Fix initialization and overflow checks */
    if xs.len() == 0 {
        return 0;
    }
    
    let mut max_sum = xs[0];
    let mut current_sum = xs[0];
    let mut best_start = 0usize;
    let mut best_len = 1usize;
    let mut current_start = 0usize;
    
    // Initialize invariants for i=1
    proof {
        lemma_spec_sum_single(xs, 0);
        assert(spec_sum(xs, 0, 1) == xs[0] as int);
    }
    
    let mut i = 1usize;
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            best_start < xs.len(),
            best_len >= 1,
            best_start + best_len <= xs.len(),
            current_start < i,
            #[verifier::truncate] max_sum == spec_sum(xs, best_start as int, best_len as int) as i32,
            #[verifier::truncate] current_sum == spec_sum(xs, current_start as int, (i - current_start) as int) as i32,
            forall|start: int, len: int|
                0 <= start < i && 
                1 <= len <= i - start
                ==> spec_sum(xs, start, len) <= max_sum as int,
        decreases xs.len() - i
    {
        if current_sum < 0 {
            current_sum = xs[i];
            current_start = i;
            proof {
                lemma_spec_sum_single(xs, i as int);
            }
        } else {
            proof {
                if current_start < i {
                    lemma_spec_sum_extend(xs, current_start as int, (i - current_start) as int);
                }
            }
            // Check for overflow before addition
            if current_sum <= i32::MAX - xs[i] && current_sum >= i32::MIN - xs[i] {
                current_sum = current_sum + xs[i];
            } else {
                current_sum = xs[i];
                current_start = i;
            }
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = current_start;
            best_len = i - current_start + 1;
        }
        
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}