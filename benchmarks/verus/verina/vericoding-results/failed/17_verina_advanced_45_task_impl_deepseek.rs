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
/* helper modified by LLM (iteration 5): fix compilation error by using proper Verus syntax for checking empty vector */
proof fn lemma_vec_is_empty(xs: &Vec<i32>) -> bool { xs.len() == 0 }

proof fn lemma_sum_properties(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len <= xs.len(),
    ensures
        spec_sum(xs, start, len) == spec_sum(xs, start, len),
    decreases len,
{
    if len > 0 {
        lemma_sum_properties(xs, start + 1, len - 1);
    }
}

proof fn lemma_vec_not_empty(xs: &Vec<i32>) -> bool { xs.len() > 0 }
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
/* code modified by LLM (iteration 5): fix compilation error by using proper Verus syntax for checking empty vector */
{
    if xs.len() == 0 {
        return 0;
    }
    
    let mut max_sum = i32::MIN;
    let n = xs.len();
    
    let mut start = 0;
    while start < n
        invariant
            0 <= start <= n,
            n > 0 ==> (
                exists|i: int, j: int| 
                    0 <= i <= start < n && 
                    1 <= j <= n - i &&
                    max_sum == spec_sum(xs, i, j) as i32
            ) &&
            (forall|i: int, j: int| 
                0 <= i <= start && 
                1 <= j <= n - i
                ==> spec_sum(xs, i, j) <= max_sum as int
            ),
    {
        let mut current_sum = 0;
        let mut end = start;
        
        while end < n
            invariant
                start <= end <= n,
                current_sum == spec_sum(xs, start as int, (end - start) as int),
                max_sum >= spec_sum(xs, start as int, (end - start) as int) as i32,
                (forall|i: int, j: int| 
                    0 <= i < start && 
                    1 <= j <= n - i
                    ==> spec_sum(xs, i, j) <= max_sum as int
                ),
        {
            current_sum = current_sum + xs[end];
            if current_sum > max_sum {
                max_sum = current_sum;
            }
            end = end + 1;
        }
        
        start = start + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}