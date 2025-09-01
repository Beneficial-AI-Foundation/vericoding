use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    if n < 2 {
        return false;
    }

    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            // If we found a pair of close elements in previous iterations, flag would be true
            // If flag is true, then such a pair exists
            // This is actually not automatically inferred from the postcondition
            // This ensures the accumulated state is consistent with the postcondition.
            exists|idx1: int, idx2: int| 0 <= idx1 && 0 <= idx2 && idx1 < n && idx2 < n && idx1 != idx2 && abs_spec(numbers[idx1] as int - numbers[idx2] as int) < threshold as int
                ==> exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold,

            // If a pair (k, l) with k < i and l < n has been found,
            // then the final flag is true
            forall|other_i: int, other_j: int| 0 <= other_i && other_i < i && 0 <= other_j && other_j < n && other_i != other_j
                ==> abs_spec(numbers[other_i] as int - numbers[other_j] as int) < threshold as int
                ==> exists|x: int, y: int| 0 <= x && 0 <= y && x < n && y < n && x != y && abs_spec(numbers[x] as int - numbers[y] as int) < threshold as int,
    {
        let mut j: int = i + 1;
        while j < n
            invariant
                0 <= i < n,
                i < j <= n,
                // Inner loop invariant: If a close pair (i, k) for k < j exists, then
                // `flag` must be true.
                // This means that if we found a pair (i,k) where k < j, then the postcondition holds.
                (exists|k: int| i < k && k < j && abs_spec(numbers[i] as int - numbers[k] as int) < threshold as int)
                    ==> (exists|x: int, y: int| 0 <= x && 0 <= y && x < n && y < n && x != y && abs_spec(numbers[x] as int - numbers[y] as int) < threshold as int),

                // This is the property that this loop is actually maintaining!
                // if there is some pair (i, k) where i < k < j such that
                // abs(numbers[i] - numbers[k]) < threshold, then the final result will be true.
                forall|k: int| i < k && k < j ==> abs_spec(numbers[i] as int - numbers[k] as int) >= threshold as int,
        {
            if abs_spec(numbers[i] as int - numbers[j] as int) < threshold as int {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}
}