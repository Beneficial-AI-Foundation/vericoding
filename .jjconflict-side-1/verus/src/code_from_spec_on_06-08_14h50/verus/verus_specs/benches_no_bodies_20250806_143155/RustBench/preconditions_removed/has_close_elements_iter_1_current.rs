use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

fn abs(i: i32) -> (res: i32)
    requires
        i != i32::MIN,
    ensures
        i < 0 ==> res == -i,
        i >= 0 ==> res == i
{
    if i < 0 {
        -i
    } else {
        i
    }
}

#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
{
    let mut i = 0;
    while i < numbers.len()
        invariant
            forall|k: int, l: int| 0 <= k < i && 0 <= l < numbers.len() && k != l ==> abs_spec(numbers[k] - numbers[l]) >= threshold
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                forall|k: int, l: int| 0 <= k < i && 0 <= l < numbers.len() && k != l ==> abs_spec(numbers[k] - numbers[l]) >= threshold,
                forall|l: int| 0 <= l < j && l != i ==> abs_spec(numbers[i] - numbers[l]) >= threshold
        {
            if i != j && abs_spec((numbers[i] - numbers[j]) as int) < threshold {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

fn main() {}
}