use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|i1: int, j1: int| 
                0 <= i1 < i && i1 < j1 < numbers@.len() ==> 
                abs(numbers[i1] - numbers[j1]) >= threshold
    {
        for j in (i + 1)..n
            invariant
                forall|j1: int| 
                    i < j1 < j ==> 
                    abs(numbers[i] - numbers[j1]) >= threshold,
                forall|i1: int, j1: int| 
                    0 <= i1 < i && i1 < j1 < numbers@.len() ==> 
                    abs(numbers[i1] - numbers[j1]) >= threshold
        {
            if abs(numbers[i] - numbers[j]) < threshold {
                assert(0 <= i < j < numbers@.len());
                assert(abs(numbers[i] - numbers[j]) < threshold);
                return true;
            }
        }
    }
    
    assert(forall|i: int, j: int| 
        0 <= i < j < numbers@.len() ==> 
        abs(numbers[i] - numbers[j]) >= threshold);
    false
}
// </vc-code>

fn main() {}
}