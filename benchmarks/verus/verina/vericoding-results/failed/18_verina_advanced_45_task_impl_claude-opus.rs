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
proof fn sum_extend(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len < xs.len(),
    ensures
        spec_sum(xs, start, len + 1) == spec_sum(xs, start, len) + xs[start + len],
    decreases len
{
    if len == 0 {
        assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
        assert(spec_sum(xs, start + 1, 0) == 0);
    } else {
        assert(spec_sum(xs, start, len + 1) == xs[start] + spec_sum(xs, start + 1, len));
        sum_extend(xs, start + 1, len - 1);
        assert(spec_sum(xs, start + 1, len) == spec_sum(xs, start + 1, len - 1) + xs[start + len]);
    }
}

/* helper modified by LLM (iteration 5): Fixed sum_bounds proof logic */
proof fn sum_bounds(xs: &Vec<i32>, start: int, len: int)
    requires
        0 <= start < xs.len(),
        1 <= len <= xs.len() - start,
    ensures
        spec_sum(xs, start, len) >= -(len * i32::MAX as int),
        spec_sum(xs, start, len) <= len * i32::MAX as int,
    decreases len
{
    if len == 1 {
        assert(spec_sum(xs, start, 1) == xs[start] + spec_sum(xs, start + 1, 0));
        assert(spec_sum(xs, start + 1, 0) == 0);
        assert(spec_sum(xs, start, 1) == xs[start]);
        assert(xs[start] >= i32::MIN);
        assert(xs[start] <= i32::MAX);
    } else {
        sum_bounds(xs, start + 1, len - 1);
        assert(spec_sum(xs, start, len) == xs[start] + spec_sum(xs, start + 1, len - 1));
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
    /* code modified by LLM (iteration 5): Fixed type errors in assertions */
    if xs.len() == 0 {
        return 0;
    }
    
    let mut max_sum: i32 = xs[0];
    assert(spec_sum(xs, 0, 1) == xs[0]);
    
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            exists|start: int, len: int|
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                max_sum == spec_sum(xs, start, len) as i32 &&
                spec_sum(xs, start, len) >= i32::MIN &&
                spec_sum(xs, start, len) <= i32::MAX,
            forall|start: int, len: int|
                0 <= start < i && 
                1 <= len <= xs.len() - start &&
                start + len <= xs.len() &&
                spec_sum(xs, start, len) >= i32::MIN &&
                spec_sum(xs, start, len) <= i32::MAX
                ==> spec_sum(xs, start, len) <= max_sum as int,
        decreases xs.len() - i
    {
        let mut j: usize = i;
        let mut current_sum: i32 = 0;
        
        while j < xs.len()
            invariant
                i <= j <= xs.len(),
                j == i ==> current_sum == 0,
                j > i ==> current_sum == spec_sum(xs, i as int, (j - i) as int) as i32,
                j > i ==> spec_sum(xs, i as int, (j - i) as int) >= i32::MIN,
                j > i ==> spec_sum(xs, i as int, (j - i) as int) <= i32::MAX,
            decreases xs.len() - j
        {
            if j < xs.len() {
                let can_add_pos = current_sum <= i32::MAX - xs[j];
                let can_add_neg = current_sum >= i32::MIN - xs[j];
                
                if xs[j] >= 0 && can_add_pos {
                    current_sum = current_sum + xs[j];
                    j = j + 1;
                    
                    proof {
                        if j - i == 1 {
                            assert(spec_sum(xs, i as int, 1) == xs[i as int]);
                        } else {
                            sum_extend(xs, i as int, ((j - 1) - i) as int);
                        }
                    }
                    
                    if current_sum > max_sum {
                        max_sum = current_sum;
                    }
                } else if xs[j] < 0 && can_add_neg {
                    current_sum = current_sum + xs[j];
                    j = j + 1;
                    
                    proof {
                        if j - i == 1 {
                            assert(spec_sum(xs, i as int, 1) == xs[i as int]);
                        } else {
                            sum_extend(xs, i as int, ((j - 1) - i) as int);
                        }
                    }
                    
                    if current_sum > max_sum {
                        max_sum = current_sum;
                    }
                } else {
                    j = xs.len();
                }
            } else {
                j = xs.len();
            }
        }
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}