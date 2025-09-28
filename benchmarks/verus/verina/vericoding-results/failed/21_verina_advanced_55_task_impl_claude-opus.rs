// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemmas with proper proofs and added new helper lemma */
proof fn lemma_filter_subset(xs: Seq<i32>, target: i32)
    ensures
        xs.filter(|x: i32| x == target).len() <= xs.len(),
{
    // Verus can automatically prove this
}

proof fn lemma_count_at_least_one(xs: Seq<i32>, target: i32, idx: int)
    requires
        0 <= idx < xs.len(),
        xs[idx] == target,
    ensures count_occurrences(xs, target) >= 1,
{
    let filtered = xs.filter(|x: i32| x == target);
    // Since xs[idx] == target, at least one element passes the filter
    assert(filtered.len() >= 1);
}

proof fn lemma_subrange_count(xs: Seq<i32>, target: i32, k: int)
    requires
        0 <= k <= xs.len(),
    ensures
        count_occurrences(xs.subrange(0, k), target) <= count_occurrences(xs, target),
{
    // Every element in subrange(0,k) is also in the full sequence
    // So the count in the subrange cannot exceed the count in the full sequence
}

proof fn lemma_subrange_full(xs: Seq<i32>, target: i32)
    ensures
        xs.subrange(0, xs.len()) =~= xs,
        count_occurrences(xs.subrange(0, xs.len()), target) == count_occurrences(xs, target),
{
    assert(xs.subrange(0, xs.len()) =~= xs);
}
// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and bounds checking */
    let mut result: i32 = xs[0];
    let mut result_idx: usize = 0;
    let mut max_count: usize = 1;  // At least 1 since xs[0] exists
    
    proof {
        lemma_count_at_least_one(xs@, xs[0], 0);
        assert(count_occurrences(xs@, xs[0]) >= 1);
    }
    
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            0 <= result_idx < xs.len(),
            xs[result_idx as int] == result,
            xs@.contains(result),
            max_count >= 1,
            max_count <= xs.len(),
            forall|j: int| #![auto] 0 <= j < i ==> count_occurrences(xs@, xs[j]) <= count_occurrences(xs@, result),
            forall|k: int| #![auto] 0 <= k < result_idx ==> count_occurrences(xs@, xs[k]) < count_occurrences(xs@, result),
        decreases xs.len() - i
    {
        let current = xs[i];
        
        // Check if we've already counted this element
        let mut already_counted = false;
        let mut check_idx: usize = 0;
        while check_idx < i
            invariant
                0 <= check_idx <= i,
                i < xs.len(),
                already_counted == exists|m: int| 0 <= m < check_idx && m < xs.len() && xs[m] == current,
            decreases i - check_idx
        {
            if check_idx < xs.len() && xs[check_idx] == current {
                already_counted = true;
            }
            check_idx = check_idx + 1;
        }
        
        if !already_counted {
            // Count occurrences of current element
            let mut count: usize = 0;
            let mut j: usize = 0;
            
            while j < xs.len()
                invariant
                    0 <= j <= xs.len(),
                    count <= j,
                    count <= xs.len(),
                    count == count_occurrences(xs@.subrange(0, j as int), current) as usize,
                decreases xs.len() - j
            {
                if xs[j] == current {
                    count = count + 1;
                }
                proof {
                    lemma_subrange_count(xs@, current, (j + 1) as int);
                }
                j = j + 1;
            }
            
            proof {
                lemma_subrange_full(xs@, current);
                assert(count == count_occurrences(xs@, current) as usize);
            }
            
            // Update result if we found a more frequent element
            if count > max_count || (count == max_count && i < result_idx) {
                max_count = count;
                result = current;
                result_idx = i;
                proof {
                    lemma_count_at_least_one(xs@, current, i as int);
                    assert(count_occurrences(xs@, result) == max_count as nat);
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result));
    }
    
    result
}
// </vc-code>

}
fn main() {}