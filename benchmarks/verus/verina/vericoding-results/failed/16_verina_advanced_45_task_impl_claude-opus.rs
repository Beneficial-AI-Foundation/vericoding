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
/* helper modified by LLM (iteration 4): Fixed lemma proofs for sum properties */
proof fn lemma_sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start < xs.len(),
        0 <= len < xs.len() - start,
    ensures
        spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len],
    decreases len
{
    if len == 0 {
        assert(spec_sum(xs, start, 0) == 0);
        assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
        assert(spec_sum(xs, start, 1) == xs[start]);
    } else {
        assert(spec_sum(xs, start, len + 1) == xs[start] + spec_sum(xs, start + 1, len));
        lemma_sum_extend(xs, start + 1, len - 1);
        assert(spec_sum(xs, start + 1, len) == spec_sum(xs, start + 1, len - 1) + xs[start + len]);
        assert(spec_sum(xs, start, len) == xs[start] + spec_sum(xs, start + 1, len - 1));
    }
}

proof fn lemma_sum_single(xs: &Vec<i32>, start: int)
    requires
        0 <= start < xs.len(),
    ensures
        spec_sum(xs, start, 1) == xs[start],
{
    assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
    assert(spec_sum(xs, start + 1, 0) == 0);
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
    /* code modified by LLM (iteration 4): Fixed type casting - using i32 directly without int casts */
    if xs.len() == 0 {
        return 0;
    }
    
    proof {
        lemma_sum_single(xs, 0);
        assert(spec_sum(xs, 0, 1) == xs[0]);
    }
    
    let mut max_ending_here: i32 = xs[0];
    let mut max_so_far: i32 = xs[0];
    let mut i: usize = 1;
    
    let mut best_start: usize = 0;
    let mut best_len: usize = 1;
    let mut current_start: usize = 0;
    let mut current_len: usize = 1;
    
    assert(max_ending_here == spec_sum(xs, current_start as int, current_len as int) as i32);
    assert(max_so_far == spec_sum(xs, best_start as int, best_len as int) as i32);
    
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            0 <= current_start < i,
            1 <= current_len <= i - current_start,
            max_ending_here == #[verifier::truncate] spec_sum(xs, current_start as int, current_len as int) as i32,
            0 <= best_start < i,
            1 <= best_len <= i - best_start,
            max_so_far == #[verifier::truncate] spec_sum(xs, best_start as int, best_len as int) as i32,
            forall|s: int, l: int| 0 <= s < i && 1 <= l <= i - s ==> spec_sum(xs, s, l) <= max_so_far as int,
            forall|l: int| 1 <= l <= i - current_start ==> spec_sum(xs, current_start as int, l) <= max_ending_here as int,
        decreases xs.len() - i
    {
        let new_val = #[verifier::truncate] (max_ending_here + xs[i]) as i32;
        if new_val > xs[i] {
            proof {
                lemma_sum_extend(xs, current_start as int, current_len as int);
                assert(spec_sum(xs, current_start as int, current_len as int + 1) == spec_sum(xs, current_start as int, current_len as int) + xs[current_start as int + current_len as int]);
            }
            max_ending_here = new_val;
            current_len = current_len + 1;
        } else {
            proof {
                lemma_sum_single(xs, i as int);
            }
            max_ending_here = xs[i];
            current_start = i;
            current_len = 1;
        }
        
        if max_ending_here > max_so_far {
            max_so_far = max_ending_here;
            best_start = current_start;
            best_len = current_len;
        }
        
        i = i + 1;
    }
    
    max_so_far
}
// </vc-code>

}
fn main() {}