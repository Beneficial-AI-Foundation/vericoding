use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
fn abs(i: i32) -> (res: i32)
    requires
        i != i32::MIN,
    ensures
        i < 0 ==> res == -i,
        i >= 0 ==> res == i,
        res == abs_spec(i as int)
{
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
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|a: int, b: int| 0 <= a < i && 0 <= b < numbers.len() && a != b ==> abs_spec(numbers[a as int] - numbers[b as int]) >= threshold
        decreases numbers.len() - i
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                0 <= j <= numbers.len(),
                forall|a: int, b: int| 0 <= a < i && 0 <= b < numbers.len() && a != b ==> abs_spec(numbers[a as int] - numbers[b as int]) >= threshold,
                forall|b: int| 0 <= b < j && i != b ==> abs_spec(numbers[i as int] - numbers[b as int]) >= threshold
            decreases numbers.len() - j
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                let abs_diff = abs(diff);
                if abs_diff < threshold {
                    return true;
                }
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