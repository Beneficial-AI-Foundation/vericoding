use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if arr.len() == 1 {
        return true;
    }

    let mut i: usize = 0;
    let mut is_consecutive = true;

    while i < arr.len() - 1
        invariant
            0 <= i < arr.len(),
            is_consecutive ==> (forall|k: int| 0 <= k < i ==> #[trigger] arr[k as usize] + 1 == arr[(k + 1) as usize]),
        decreases arr.len() - 1 - i
    {
        if arr[i] != arr[i + 1] - 1 {
            is_consecutive = false;
        }
        i = i + 1;
    }

    is_consecutive
}
// </vc-code>

} // verus!

fn main() {}