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
/* helper modified by LLM (iteration 5): provided actual proofs for lemmas using spec_sum definition */
proof fn lemma_spec_sum_single(xs: &Vec<i32>, start: int)
    requires
        0 <= start < xs.len(),
    ensures
        spec_sum(xs, start, 1) == xs[start],
{
    // By definition of spec_sum with len = 1
    assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
    assert(spec_sum(xs, start + 1, 0) == 0);
}

proof fn lemma_spec_sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start < xs.len(),
        len > 0,
        start + len < xs.len(),
    ensures
        spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len],
{
    // Proof by induction on len
    if len == 1 {
        assert(spec_sum(xs, start, 2) == xs[start] + spec_sum(xs, start + 1, 1));
        lemma_spec_sum_single(xs, start + 1);
        assert(spec_sum(xs, start + 1, 1) == xs[start + 1]);
        assert(spec_sum(xs, start, 1) == xs[start]);
    } else {
        assert(spec_sum(xs, start, len + 1) == xs[start] + spec_sum(xs, start + 1, len));
        lemma_spec_sum_extend(xs, start + 1, len - 1);
    }
}

proof fn lemma_spec_sum_bounds(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start < xs.len(),
        1 <= len <= xs.len() - start,
        forall|k: int| 0 <= k < xs.len() ==> -2147483648 <= xs[k] <= 2147483647,
    ensures
        spec_sum(xs, start, len) >= len * (-2147483648),
        spec_sum(xs, start, len) <= len * 2147483647,
{
    if len == 1 {
        lemma_spec_sum_single(xs, start);
    } else {
        lemma_spec_sum_bounds(xs, start + 1, len - 1);
        lemma_spec_sum_extend(xs, start, len - 1);
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
    /* code modified by LLM (iteration 5): simplified implementation to handle basic cases and prove invariants */
    if xs.len() == 0 {
        return 0;
    }
    
    let mut max_sum = xs[0];
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            i == 0 ==> max_sum == xs[0],
            i > 0 ==> (
                exists|start: int, len: int|
                    0 <= start < i &&
                    1 <= len <= i - start &&
                    max_sum == spec_sum(xs, start, len) as i32
            ),
            forall|start: int, len: int|
                0 <= start < i &&
                1 <= len <= i - start
                ==> spec_sum(xs, start, len) <= max_sum as int,
        decreases xs.len() - i
    {
        if i == 0 {
            proof {
                lemma_spec_sum_single(xs, 0);
            }
        }
        
        let mut current_sum = xs[i];
        let mut best_ending_here = xs[i];
        
        let mut j = i;
        while j > 0
            invariant
                0 <= j <= i,
                current_sum == spec_sum(xs, j, (i - j + 1) as int),
            decreases j
        {
            j -= 1;
            current_sum = current_sum + xs[j];
            if current_sum > best_ending_here {
                best_ending_here = current_sum;
            }
            proof {
                if j < xs.len() - 1 {
                    lemma_spec_sum_extend(xs, j, (i - j) as int);
                }
            }
        }
        
        if best_ending_here > max_sum {
            max_sum = best_ending_here;
        }
        
        i += 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}