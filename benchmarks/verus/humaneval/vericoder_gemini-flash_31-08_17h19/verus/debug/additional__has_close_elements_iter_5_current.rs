use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>

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

    let mut i: usize = 0;
    while (i as int) < (n as int)
        invariant
            0 <= i as int, i as int <= n as int,
            // (1)
            // If there exists a pair (idx1, idx2) of close elements where idx1 < i and idx2 < n,
            // then `has_close_elements` should eventually return true once such a pair is found.
            // This invariant ensures that if a close pair was found in previous
            // outer loop iterations, the fact is preserved.
            (exists|idx1: int, idx2: int| 0 <= idx1 && idx1 < i as int && 0 <= idx2 && idx2 < n as int
                && idx1 != idx2 && abs_spec(numbers[idx1 as usize] as int - numbers[idx2 as usize] as int) < threshold as int)
                ==> (exists|x: int, y: int| 0 <= x && x < n as int && 0 <= y && y < n as int
                && x != y && abs_spec(numbers[x as usize] as int - numbers[y as usize] as int) < threshold as int),

            // This ensures that the elements considered so far do not contain a close pair
            // (i.e. numbers[idx1], numbers[idx2]) for idx1 < i, idx2 < n, if we haven't returned true.
            forall|x: int, y: int| 0 <= x && x < i as int && 0 <= y && y < n as int && x != y ==>
                abs_spec(numbers[x as usize] as int - numbers[y as usize] as int) >= threshold as int,
    {
        let mut j: usize = i + 1;
        while (j as int) < (n as int)
            invariant
                0 <= i as int, i as int < n as int,
                i as int < j as int, j as int <= n as int,
                // (1)
                // If there exists a pair numbers[i], numbers[k] with i < k < j that are close,
                // then has_close_elements should eventually return true once such a pair is found.
                // This invariant states that if such a pair was found in a
                // previous inner loop iteration, the fact is preserved.
                (exists|k: int| i as int < k && k < j as int && abs_spec(numbers[i as usize] as int - numbers[k as usize] as int) < threshold as int)
                    ==> (exists|x: int, y: int| 0 <= x && 0 <= y && x < n as int && y < n as int
                    && x != y && abs_spec(numbers[x as usize] as int - numbers[y as usize] as int) < threshold as int),

                // This ensures that for the current `i`, the elements numbers[k] where i < k < j
                // do not form a close pair with numbers[i], if we haven't returned true.
                forall|k: int| i as int < k && k < j as int ==> abs_spec(numbers[i as usize] as int - numbers[k as usize] as int) >= threshold as int,
        {
            if abs_spec(numbers[i as usize] as int - numbers[j as usize] as int) < threshold as int {
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