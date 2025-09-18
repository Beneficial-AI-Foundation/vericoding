// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and indexing */
proof fn count_true_nonnegative(condition: Seq<bool>) 
    ensures count_true(condition) >= 0
    decreases condition.len()
{
    if condition.len() == 0 {
    } else {
        count_true_nonnegative(condition.skip(1));
    }
}

/* helper modified by LLM (iteration 5): Fixed indexing with proper usize casts */
proof fn find_index(condition: Seq<bool>, idx: int) -> (pos: nat)
    requires 0 <= idx < count_true(condition)
    ensures 0 <= pos < condition.len(),
            condition[pos],
            count_true(condition.subrange(0, pos as int)) == idx
    decreases condition.len()
{
    if condition.len() == 0 {
        assert(false);
        0
    } else if condition[0] {
        if idx == 0 {
            0
        } else {
            let sub_index = find_index(condition.skip(1), idx - 1);
            assert(1 + sub_index < condition.len());
            1 + sub_index
        }
    } else {
        let sub_index = find_index(condition.skip(1), idx);
        assert(1 + sub_index < condition.len());
        1 + sub_index
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
    /* code modified by LLM (iteration 5): Fixed vector indexing with proper usize casting */
    let mut result = Vec::new();
    let count: int = count_true(condition@);
    let mut j: int = 0;
    while j < count
        invariant 
            0 <= j <= count,
            result.len() as int == j,
            forall|k: int| 0 <= k < j ==> 
                #[trigger] result[k as usize] == arr[find_index(condition@, k) as usize]
    {
        let pos = find_index(condition@, j);
        result.push(arr[pos as usize]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}