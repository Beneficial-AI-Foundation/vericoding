use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_arr_bounds(arr: &Vec<Vec<i32>>, i: int)
    requires
        0 <= i < arr.len(),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k].len() > 0,
    ensures
        i < arr@.len(),
        arr@[i].len() > 0,
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 5): fixed type mismatches by casting i to int for lemma call and sequence indexing */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == #[trigger] arr@[j]@[0],
        decreases arr.len() - i,
    {
        proof {
            lemma_arr_bounds(arr, i as int);
            assert(0 <= i < arr.len());
            assert(arr@[i as int].len() > 0);
            assert(i < arr@.len());
        }
        result.push(arr[i as usize][0]);
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}