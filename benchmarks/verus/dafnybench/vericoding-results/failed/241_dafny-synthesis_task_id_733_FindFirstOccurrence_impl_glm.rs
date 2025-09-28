use vstd::prelude::*;

verus! {

// <vc-helpers>

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
            forall|j: int| 0 <= j < i ==> arr[j] != target
    {
        if arr[i] == target {
            return i as i32;
        } else if arr[i] > target {
            ghost {
                assert forall|j: int| i <= j < arr.len() ==> arr[j] != target
                by {
                    if i <= j < arr.len() {
                        if i == j {
                            assert(arr[i] > target);
                        } else {
                            assert(arr[i] <= arr[j]); 
                            assert(arr[j] >= arr[i]);
                            assert(arr[i] > target);
                            assert(arr[j] > target);
                        }
                    }
                }
            }
            break;
        }
        i += 1;
    }
    -1
}
// </vc-code>

fn main() {
}

}