// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|a: int, b: int| 0 <= a && a < i && 0 <= b && b < n && a != b ==> abs_spec(numbers[a] - numbers[b]) >= threshold
    {
        for j in 0..n
            invariant
                forall|b: int| 0 <= b && b < j && i != b ==> abs_spec(numbers[i as int] - numbers[b]) >= threshold,
                forall|a: int, b: int| 0 <= a && a < i && 0 <= b && b < n && a != b ==> abs_spec(numbers[a] - numbers[b]) >= threshold
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                if diff < 0 {
                    if -diff < threshold {
                        return true;
                    }
                } else {
                    if diff < threshold {
                        return true;
                    }
                }
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}