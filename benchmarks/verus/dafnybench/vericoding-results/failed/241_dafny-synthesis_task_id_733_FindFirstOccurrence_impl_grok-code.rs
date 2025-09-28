use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
//
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &[i32], target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (0 <= result < arr.len() ==> arr[result as int] == target) &&
        (result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target)
// </vc-spec>
// <vc-code>
{
proof {
    assert(arr@.len() == (arr.len() as int));
    assert(arr.len() <= 2147483647);
}
let mut i: usize = 0;
while i < arr.len()
    invariant
        0 <= (i as int) <= (arr.len() as int),
        forall|k: int| 0 <= k < (i as int) ==> arr@[k] != target
    decreases ((arr.len() - i) as int)
{
    if arr[i] == target {
        return #[verifier::truncate] (i as i32);
    }
    i += 1;
}
return -1;
}
// </vc-code>

fn main() {
}

}