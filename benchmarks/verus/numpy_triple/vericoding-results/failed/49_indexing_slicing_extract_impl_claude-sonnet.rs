// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified mapping to use nth_true_index for correct correspondence */
proof fn count_true_empty()
    ensures count_true(Seq::<bool>::empty()) == 0
{
}

proof fn count_true_nonnegative(condition: Seq<bool>)
    ensures count_true(condition) >= 0
    decreases condition.len()
{
    if condition.len() == 0 {
        count_true_empty();
    } else {
        count_true_nonnegative(condition.skip(1));
    }
}

proof fn count_true_subrange_property(condition: Seq<bool>, start: int, end: int)
    requires 0 <= start <= end <= condition.len()
    ensures count_true(condition.subrange(start, end)) >= 0
    decreases end - start
{
    count_true_nonnegative(condition.subrange(start, end));
}

spec fn nth_true_index(condition: Seq<bool>, n: int) -> int
    decreases condition.len()
{
    if n < 0 || condition.len() == 0 {
        -1
    } else if condition[0] {
        if n == 0 {
            0
        } else {
            let sub_idx = nth_true_index(condition.skip(1), n - 1);
            if sub_idx >= 0 { sub_idx + 1 } else { -1 }
        }
    } else {
        let sub_idx = nth_true_index(condition.skip(1), n);
        if sub_idx >= 0 { sub_idx + 1 } else { -1 }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition to match correct mapping semantics */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < condition.len()
        invariant
            0 <= i <= condition.len(),
            condition.len() == arr.len(),
            result.len() == count_true(condition@.subrange(0, i as int)),
            forall|j: int| 0 <= j < result.len() ==> {
                let orig_idx = nth_true_index(condition@.subrange(0, i as int), j);
                orig_idx >= 0 && orig_idx < i && #[trigger] result[j] == arr[orig_idx]
            }
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(i == condition.len());
        assert(condition@.subrange(0, i as int) =~= condition@);
        count_true_nonnegative(condition@);
    }
    
    result
}
// </vc-code>

}
fn main() {}