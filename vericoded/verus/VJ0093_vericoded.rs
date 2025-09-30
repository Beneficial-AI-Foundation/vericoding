// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)

    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,

    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added invariant to carry function precondition through the loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < arr.len() ==> arr[k].len() > 0,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == arr@[j]@[0],
        decreases arr.len() - i
    {
        result.push(arr[i][0]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}