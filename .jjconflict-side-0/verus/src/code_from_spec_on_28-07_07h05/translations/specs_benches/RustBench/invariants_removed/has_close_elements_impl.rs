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
            0 <= i <= numbers.len(),
            /* code modified by LLM (iteration 1): Fixed loop invariant to use int indices directly without usize casting */
            forall|k: int, l: int| 0 <= k < i && 0 <= l < numbers.len() && k != l ==> abs_spec(numbers[k] - numbers[l]) >= threshold
        /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
        decreases numbers.len() - i
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                0 <= j <= numbers.len(),
                /* code modified by LLM (iteration 1): Fixed loop invariant to use int indices directly without usize casting */
                forall|k: int, l: int| 0 <= k < i && 0 <= l < numbers.len() && k != l ==> abs_spec(numbers[k] - numbers[l]) >= threshold,
                /* code modified by LLM (iteration 1): Fixed loop invariant to use int indices directly without usize casting */
                forall|l: int| 0 <= l < j && i != l ==> abs_spec(numbers[i as int] - numbers[l]) >= threshold
            /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
            decreases numbers.len() - j
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                /* code modified by LLM (iteration 1): Simplified absolute value computation */
                let abs_diff = if diff < 0 { -diff } else { diff };
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