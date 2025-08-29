use vstd::prelude::*;


verus! {

// <vc-helpers>
proof fn lemma_min_exists(arr: &Vec<Vec<i32>>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int| 0 <= i < arr.len() && (forall|j: int| 0 <= j < arr.len() ==> arr[i][1] <= #[trigger] arr[j][1])
{
    let mut min_idx: usize = 0;
    let mut k: usize = 1;
    
    while k < arr.len()
        invariant
            0 <= min_idx < arr.len(),
            1 <= k <= arr.len(),
            forall|i: int| 0 <= i < k ==> arr[min_idx as int][1] <= #[trigger] arr[i][1],
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    {
        if arr[k as int][1] < arr[min_idx as int][1] {
            min_idx = k;
        }
        k = k + 1;
    }
}
// </vc-helpers>

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
    proof {
        lemma_min_exists(arr);
    }
    
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= min_idx < arr.len(),
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[min_idx as int][1] <= #[trigger] arr[j][1],
            forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k].len() >= 2,
    {
        /* code modified by LLM (iteration 5): remove int cast from executable code */
        if arr[i][1] < arr[min_idx][1] {
            min_idx = i;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 5): remove int cast from executable code */
    arr[min_idx][0]
}
// </vc-code>

} // verus!

fn main() {}