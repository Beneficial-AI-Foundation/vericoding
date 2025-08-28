use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helper code, spec functions, or proofs
// </vc-helpers>

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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: usize| 0 <= j < i ==> #[trigger] result[j] == #[trigger] arr[j][0],
    {
        result.push(arr[i][0]);
        i = i + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}