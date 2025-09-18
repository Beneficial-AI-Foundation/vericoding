// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to help prove count relationships */
spec fn count_prefix(xs: Seq<i32>, target: i32, end: int) -> nat {
    if 0 <= end <= xs.len() {
        xs.subrange(0, end).filter(|x: i32| x == target).len()
    } else {
        0
    }
}

proof fn lemma_count_prefix_equals_count_occurrences(xs: Seq<i32>, target: i32)
    ensures count_prefix(xs, target, xs.len() as int) == count_occurrences(xs, target)
{
    assert(xs.subrange(0, xs.len() as int) == xs);
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
    /* code modified by LLM (iteration 5): fixed bounds checks and integer overflow */
    let mut max_count: usize = 1;
    let mut result = xs[0];
    let mut result_idx: usize = 0;
    
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            xs@.contains(result),
            0 <= result_idx < xs.len(),
            xs@[result_idx as int] == result,
            max_count == count_occurrences(xs@, result),
            max_count >= 1,
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) <= max_count,
            forall|j: int| 0 <= j < result_idx ==> count_occurrences(xs@, xs@[j]) < max_count,
        decreases xs.len() - i
    {
        let current_elem = xs[i];
        let mut count: usize = 0;
        let mut k: usize = 0;
        while k < xs.len()
            invariant
                0 <= k <= xs.len(),
                count == count_prefix(xs@, current_elem, k as int),
                count <= xs.len(),
            decreases xs.len() - k
        {
            if xs[k] == current_elem {
                count = count + 1;
            }
            k = k + 1;
        }
        
        proof {
            lemma_count_prefix_equals_count_occurrences(xs@, current_elem);
        }
        
        if count > max_count {
            max_count = count;
            result = current_elem;
            result_idx = i;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}