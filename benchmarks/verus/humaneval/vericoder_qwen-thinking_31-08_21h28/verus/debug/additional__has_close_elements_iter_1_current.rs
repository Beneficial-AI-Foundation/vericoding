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
    if numbers.len() < 2 {
        return false;
    }
    let n = numbers.len();
    let mut sorted = numbers.to_vec();
    sorted.sort();
    let mut i = 0;
    while i < n - 1 {
        invariant(forall |j: int| 0 <= j && j < (i as int) ==> sorted[(j as usize) + 1] - sorted[j as usize] >= threshold)
        if sorted[i+1] - sorted[i] < threshold {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}