use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn helpers_dummy() {}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|j: int| 0 <= j && j < i as int ==> arr[j as int] != target,
        decreases arr.len() - i
    {
        if arr[i] == target {
            assert(i < arr.len());
            assert(arr.len() > 0);
            return Some(i);
        }
        i += 1;
    }
    assert(i == arr.len());
    None
}
// </vc-code>

fn main() {}
}