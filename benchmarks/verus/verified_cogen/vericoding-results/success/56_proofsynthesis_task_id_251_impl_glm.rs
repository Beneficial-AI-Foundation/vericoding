// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)

    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add decreases clause to loop */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            result@.len() == 2 * i,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] result@[2 * k] == elem,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] result@[2 * k + 1] == arr@[k],
        decreases arr.len() - i
    {
        result.push(elem);
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}