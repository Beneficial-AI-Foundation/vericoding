use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    for i in 0..n {
        invariant(
            forall (i0: int) ::
                (0 <= i0 < i) ==>
                forall (j0: int) ::
                    #[trigger] (abs(numbers[i0] - numbers[j0]) < threshold && i0 < j0 && j0 < n) ==>
                    false
        );
        for j in i+1..n {
            invariant(
                forall (j0: int) ::
                    #[trigger] (abs(numbers[i] - numbers[j0]) < threshold && i+1 <= j0 && j0 < j) ==>
                    false
            );
            if abs(numbers[i] - numbers[j]) < threshold {
                return true;
            }
        }
    }
    false
}
// </vc-code>

fn main() {}
}