use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] arr[j] != target,
        decreases arr.len() - i
    {
        if arr[i] == target {
            let r: i32 = i as i32;
            proof {
                assert(0 <= r as int);
                assert((r as int) < arr.len());
                assert(arr[r as int] == target);
            }
            return r;
        } else {
            i = i + 1;
        }
    }
    proof {
        assert(!(i < arr.len()));
        assert(i <= arr.len());
        assert(i == arr.len());
        assert forall|k: int| 0 <= k < arr.len() ==> #[trigger] arr[k] != target by {
            if 0 <= k && k < arr.len() {
                assert(0 <= k < i as int);
                assert(arr[k] != target);
            }
        }
    }
    -1
}
// </vc-code>

fn main() {
}

}