use vstd::prelude::*;


verus! {

// <vc-helpers>
proof fn lemma_min_exists(arr: &Vec<Vec<i32>>) -> (min_idx: usize)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        min_idx < arr.len(),
        forall|j: int| 0 <= j < arr.len() ==> arr[min_idx as int][1] <= #[trigger] arr[j][1],
{
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= min_idx < arr.len(),
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[min_idx as int][1] <= #[trigger] arr[j][1],
    {
        if arr[i as int][1] < arr[min_idx as int][1] {
            min_idx = i;
        }
        i += 1;
    }
    
    min_idx
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= min_idx < arr.len(),
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr@[min_idx as int]@[1] <= #[trigger] arr@[j]@[1],
    {
        /* code modified by LLM (iteration 5): use @ for vector access instead of casting to int */
        if arr@[i as int]@[1] < arr@[min_idx as int]@[1] {
            min_idx = i;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): use @ for vector access instead of casting to int */
    arr@[min_idx as int]@[0]
}
// </vc-code>

} // verus!

fn main() {}