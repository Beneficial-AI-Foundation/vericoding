use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..arr.len()
        invariant
            result@.len() == 2 * i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k + 1] == arr[k],
    {
        result.push(elem);
        result.push(arr[i]);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}