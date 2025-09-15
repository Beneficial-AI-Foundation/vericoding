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
/* helper modified by LLM (iteration 5): strengthened proof with explicit assertions and fixed recursive proof */
spec fn is_valid_range(xs: &Vec<i32>, start: int, len: int) -> bool {
    0 <= start && start < xs.len() && 1 <= len && start + len <= xs.len()
}

proof fn spec_sum_bounds(xs: &Vec<i32>, start: int, len: int)
    requires is_valid_range(xs, start, len)
    ensures spec_sum(xs, start, len) <= i32::MAX as int && spec_sum(xs, start, len) >= i32::MIN as int
    decreases len
{
    if len == 1 {
        assert(xs[start] <= i32::MAX);
        assert(xs[start] >= i32::MIN);
        assert(spec_sum(xs, start, 1) == xs[start]);
    } else {
        assert(is_valid_range(xs, start + 1, len - 1));
        spec_sum_bounds(xs, start + 1, len - 1);
        assert(xs[start] <= i32::MAX && xs[start] >= i32::MIN);
        assert(spec_sum(xs, start + 1, len - 1) <= i32::MAX as int);
        assert(spec_sum(xs, start + 1, len - 1) >= i32::MIN as int);
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
/* code modified by LLM (iteration 5): fixed type casting issue by using usize indices directly */
{
    if xs.len() == 0 {
        return 0;
    }
    
    let mut max_sum = xs[0];
    
    for i in 0..xs.len()
        invariant
            xs.len() > 0,
            0 <= i <= xs.len(),
            exists|start: int, len: int| 
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                max_sum == spec_sum(xs, start, len) as i32,
            forall|start: int, len: int|
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                start + len <= i
                ==> spec_sum(xs, start, len) <= max_sum as int
    {
        if i == 0 {
            max_sum = xs[0];
        } else {
            let mut current_sum = xs[i];
            for j in 0..i
                invariant
                    0 <= j <= i,
                    current_sum == spec_sum(xs, (i - j) as int, (j + 1) as int)
            {
                current_sum = current_sum + xs[i - j - 1];
            }
            if current_sum > max_sum {
                max_sum = current_sum;
            }
        }
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}