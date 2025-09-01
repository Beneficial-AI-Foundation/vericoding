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
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < i && k < l < n ==> abs_spec(numbers[k] - numbers[l]) >= threshold
    {
        let mut j = i + 1;
        while j < n
            invariant
                0 <= i < j <= n,
                forall|k: int, l: int| 0 <= k < i && k < l < n ==> abs_spec(numbers[k] - numbers[l]) >= threshold,
                forall|l: int| i+1 <= l < j ==> abs_spec(numbers[i] - numbers[l]) >= threshold
        {
            let a = numbers[i];
            let b = numbers[j];
            let d_abs = if a >= b { a - b } else { b - a };
            if d_abs < threshold {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}
}