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
spec fn vec_to_seq_int(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == numbers.len() &&
        (numbers.len() == 0 ==> result.len() == 0) &&
        (numbers.len() > 0 ==> result.len() > 0) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            result[i] as int == max_up_to(vec_to_seq_int(numbers), i)) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            forall|j: int| #![trigger numbers@[j]] 0 <= j <= i ==> numbers@[j] as int <= result[i] as int) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            exists|j: int| 0 <= j <= i && numbers@[j] as int == result[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting in invariant. */
{
    let mut result: Vec<i8> = Vec::new();

    if numbers.len() == 0 {
        return result;
    }

    let mut current_max: i8 = numbers[0];
    result.push(current_max);

    let mut i: usize = 1;

    while i < numbers.len()
        invariant
            1 <= i as int,
            i <= numbers.len(),
            result.len() == i,
            // ghost state to prove max_up_to logic
            current_max as int == max_up_to(vec_to_seq_int(numbers), (i - 1) as int),
            forall|k: int| 0 <= k < i as int ==> 
                result[k as usize] as int == max_up_to(vec_to_seq_int(numbers), k)
        decreases numbers.len() - i
    {
        current_max = if numbers[i] > current_max { numbers[i] } else { current_max };
        result.push(current_max);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}