use vstd::math::abs;
use vstd::prelude::*;

verus! {
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
{
    let mut i = 0;
    while i < numbers.len()
        invariant
            forall|x: int, y: int| 0 <= x < i && x < y < numbers@.len() ==> abs(numbers[x] - numbers[y]) >= threshold,
        /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
        decreases numbers@.len() - i
    {
        let mut j = i + 1;
        while j < numbers.len()
            invariant
                i < numbers@.len(),
                i + 1 <= j <= numbers@.len(),
                forall|x: int, y: int| 0 <= x < i && x < y < numbers@.len() ==> abs(numbers[x] - numbers[y]) >= threshold,
                forall|y: int| i < y < j ==> abs(numbers[i as int] - numbers[y]) >= threshold,
            /* code modified by LLM (iteration 1): Added decreases clause to prove inner loop termination */
            decreases numbers@.len() - j
        {
            /* code modified by LLM (iteration 2): Use abs function directly to avoid underflow/overflow issues */
            let diff = abs(numbers[i] - numbers[j]);
            if diff < threshold {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

}
fn main() {}