// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_up_to(numbers: Seq<int>, index: int) -> int
    decreases index when 0 <= index < numbers.len()
{
    if 0 <= index < numbers.len() {
        if index == 0 {
            numbers[0]
        } else {
            let prev_max = max_up_to(numbers, index - 1);
            if numbers[index] > prev_max { numbers[index] } else { prev_max }
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    ensures 
        result.len() == numbers.len() &&
        (numbers.len() == 0 ==> result.len() == 0) &&
        (numbers.len() > 0 ==> result.len() > 0) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            result[i] == max_up_to(numbers, i)) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            forall|j: int| #![trigger numbers[j]] 0 <= j <= i ==> numbers[j] <= result[i]) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            exists|j: int| 0 <= j <= i && numbers[j] == result[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}