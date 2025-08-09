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

fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
{
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            forall|x: int, y: int| 0 <= x && x < i && 0 <= y && y < numbers.len() && x != y ==> abs_spec(numbers[x] - numbers[y]) >= threshold
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= i && i < numbers.len(),
                0 <= j && j <= numbers.len(),
                forall|x: int, y: int| 0 <= x && x < i && 0 <= y && y < numbers.len() && x != y ==> abs_spec(numbers[x] - numbers[y]) >= threshold,
                forall|y: int| 0 <= y && y < j && i != y ==> abs_spec(numbers[i] - numbers[y]) >= threshold
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                let abs_diff = abs_spec(diff);
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

fn main() {}
}