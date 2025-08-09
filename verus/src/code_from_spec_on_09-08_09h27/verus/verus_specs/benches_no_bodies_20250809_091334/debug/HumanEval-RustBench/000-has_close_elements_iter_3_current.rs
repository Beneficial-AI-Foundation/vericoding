use vstd::math::abs;
use vstd::prelude::*;

verus! {
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers@[i] - numbers@[j]) < threshold,
    // post-conditions-end
{
    let len = numbers.len();
    
    for i in 0..len
        invariant
            forall|ii: int, jj: int| 0 <= ii < jj < numbers@.len() && ii < i ==> abs(numbers@[ii] - numbers@[jj]) >= threshold,
    {
        for j in (i + 1)..len
            invariant
                forall|ii: int, jj: int| 0 <= ii < jj < numbers@.len() && ii < i ==> abs(numbers@[ii] - numbers@[jj]) >= threshold,
                forall|jj: int| i < jj < j ==> abs(numbers@[i as int] - numbers@[jj]) >= threshold,
        {
            /* code modified by LLM (iteration 1): Fixed indexing to use direct array access instead of sequence view with int conversion */
            if abs(numbers[i] - numbers[j]) < threshold {
                return true;
            }
        }
    }
    
    false
}

}
fn main() {}