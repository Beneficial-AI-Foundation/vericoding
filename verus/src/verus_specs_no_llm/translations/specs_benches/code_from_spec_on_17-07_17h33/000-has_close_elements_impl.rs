use vstd::math::abs;
use vstd::prelude::*;

verus! {

fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
{
    /* code modified by LLM (iteration 1): Fixed type mismatches - cast usize indices to int for array access, cast i64 values to int for abs function, and cast threshold to nat for comparison */
    let len = numbers.len();
    for i in 0..len
        invariant
            forall|ii: int, jj: int| 0 <= ii < jj < i && abs(numbers[ii] - numbers[jj]) >= threshold,
    {
        for j in (i + 1)..len
            invariant
                forall|ii: int, jj: int| 0 <= ii < jj < i && abs(numbers[ii] - numbers[jj]) >= threshold,
                forall|jj: int| (i + 1) <= jj < j && abs(numbers[ii as int] - numbers[jj]) >= threshold,
        {
            if abs(numbers[i as int] - numbers[j as int]) < threshold as nat {
                return true;
            }
        }
    }
    false
}

}

fn main() {}