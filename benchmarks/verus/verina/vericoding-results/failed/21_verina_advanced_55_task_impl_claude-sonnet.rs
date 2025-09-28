// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed proof logic and added proper incremental proof */
proof fn count_occurrences_of_element_at_index(xs: Seq<i32>, idx: int, target: i32)
    requires 0 <= idx < xs.len(), xs[idx] == target
    ensures count_occurrences(xs, target) >= 1
{
    let filtered = xs.filter(|x: i32| x == target);
    assert(xs.contains(target));
}

proof fn count_occurrences_monotonic(xs: Seq<i32>, target1: i32, target2: i32, idx: int)
    requires 
        0 <= idx < xs.len(),
        xs[idx] == target1,
        count_occurrences(xs, target1) > count_occurrences(xs, target2)
    ensures count_occurrences(xs, target1) >= count_occurrences(xs, target2)
{
}

proof fn element_exists_in_sequence(xs: Seq<i32>, idx: int)
    requires 0 <= idx < xs.len()
    ensures xs.contains(xs[idx])
{
}

proof fn count_occurrences_subrange_lemma(xs: Seq<i32>, target: i32)
    requires xs.len() > 0
    ensures count_occurrences(xs.subrange(0, xs.len() as int), target) == count_occurrences(xs, target)
{
    assert(xs.subrange(0, xs.len() as int) == xs);
}

proof fn count_occurrences_subrange_incremental(xs: Seq<i32>, target: i32, j: int)
    requires 0 <= j < xs.len()
    ensures count_occurrences(xs.subrange(0, j + 1), target) == 
            count_occurrences(xs.subrange(0, j), target) + (if xs[j] == target { 1nat } else { 0nat })
{
    let sub1 = xs.subrange(0, j + 1);
    let sub2 = xs.subrange(0, j);
    assert(sub1 == sub2.push(xs[j]));
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
    /* code modified by LLM (iteration 5): simplified invariants and fixed initialization */
    let mut max_count: usize = 0;
    let mut result = xs[0];
    let mut result_first_idx: usize = 0;
    
    let mut i = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            0 <= result_first_idx < xs.len(),
            xs[result_first_idx as int] == result,
            max_count == count_occurrences(xs@, result),
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs[j]) <= max_count,
        decreases xs.len() - i
    {
        let mut count = 0;
        let current = xs[i];
        
        let mut j = 0;
        while j < xs.len()
            invariant
                0 <= j <= xs.len(),
                count == count_occurrences(xs@.subrange(0, j as int), current),
            decreases xs.len() - j
        {
            if xs[j] == current {
                count += 1;
            }
            j += 1;
            
            proof {
                if j > 0 {
                    count_occurrences_subrange_incremental(xs@, current, (j-1) as int);
                }
            }
        }
        
        proof {
            count_occurrences_subrange_lemma(xs@, current);
            assert(count == count_occurrences(xs@, current));
        }
        
        if count > max_count || (i == 0) {
            max_count = count;
            result = current;
            result_first_idx = i;
        }
        
        i += 1;
    }
    
    proof {
        element_exists_in_sequence(xs@, result_first_idx as int);
        count_occurrences_of_element_at_index(xs@, result_first_idx as int, result);
    }
    
    result
}
// </vc-code>

}
fn main() {}