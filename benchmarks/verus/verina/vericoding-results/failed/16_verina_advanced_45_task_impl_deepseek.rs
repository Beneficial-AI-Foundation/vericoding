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
/* helper modified by LLM (iteration 2): Fixed max_spec and prefix_sum_lemma */
spec fn max_spec(start: int, len: int, xs: &Vec<i32>) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        let max_val = max_spec(start, len - 1, xs);
        if xs[start + len - 1] as int > max_val {
            xs[start + len - 1] as int
        } else {
            max_val
        }
    }
}

proof fn prefix_sum_lemma(xs: &Vec<i32>, i: int, j: int)
    requires
        0 <= i <= j <= xs.len()
    ensures
        spec_sum(xs, i, j - i) <= max_spec(i, j - i, xs)
    decreases j - i
{
    if i < j {
        prefix_sum_lemma(xs, i, j - 1);
        assert(xs[j - 1] as int <= max_spec(i, j - i, xs));
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
/* code modified by LLM (iteration 2): Fixed loop invariants and arithmetic */
{
    if xs.len() == 0 {
        return 0;
    }
    
    let mut current_sum = 0;
    let mut max_sum = xs[0];
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            current_sum >= 0,
            exists|start: int, len: int| 
                0 <= start <= i && 
                0 <= len <= i - start &&
                max_sum == spec_sum(xs, start, len) as i32,
            (forall|start: int, len: int|
                0 <= start <= i && 
                0 <= len <= i - start
                ==> spec_sum(xs, start, len) <= max_sum as int
            )
        decreases xs.len() - i
    {
        current_sum = current_sum + xs[i] as i32;
        if current_sum < 0 {
            current_sum = 0;
        }
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}