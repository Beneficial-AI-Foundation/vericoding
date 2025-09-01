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
                0 <= i1 < i as int && i1 < j1 < numbers@.len() ==> 
                abs(numbers@[i1] - numbers@[j1]) >= threshold as int
    {
        for j in (i + 1)..n
            invariant
                forall|j1: int| 
                    i as int < j1 && j1 < j as int ==> 
                    abs(numbers@[i as int] - numbers@[j1]) >= threshold as int,
                forall|i1: int, j1: int| 
                    0 <= i1 < i as int && i1 < j1 < numbers@.len() ==> 
                    abs(numbers@[i1] - numbers@[j1]) >= threshold as int
        {
            if abs((numbers[i] - numbers[j]) as int) < threshold as int {
                assert(0 <= i as int && (i as int) < (j as int) && (j as int) < numbers@.len());
                assert(abs(numbers@[i as int] - numbers@[j as int]) < threshold as int);
                return true;
            }
        }
    }
    
    assert(forall|i: int, j: int| 
        0 <= i < j < numbers@.len() ==> 
        abs(numbers@[i] - numbers@[j]) >= threshold as int);
    false
}
// </vc-code>

fn main() {}
}