// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replace mutable sort with immutable sorted iterator to avoid &mut parameter issue */
spec fn is_sorted(arr: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < arr.len() - 1 ==> #[trigger] arr[i] <= arr[i + 1]
}

spec fn contains_same_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> bool {
    forall|x: i32| arr1@.contains(x) <==> arr2@.contains(x)
}

fn unique_sorted_impl(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        is_sorted(&result),
        contains_same_elements(arr, &result),
{
    if arr.is_empty() {
        Vec::new()
    } else {
        let sorted: Vec<i32> = arr.iter().cloned().sorted().collect();
        let mut result = Vec::new();
        result.push(sorted[0]);
        let mut i = 1;
        while i < sorted.len()
            invariant
                1 <= i <= sorted.len(),
                result.len() <= i,
                is_sorted(&result),
                forall|x: i32| sorted@.subrange(0, i as int).contains(x) <==> result@.contains(x),
            decreases sorted.len() - i
        {
            if sorted[i] != result[result.len() - 1] {
                result.push(sorted[i]);
            }
            i += 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call the fixed helper function */
    unique_sorted_impl(arr)
}
// </vc-code>

}
fn main() {}