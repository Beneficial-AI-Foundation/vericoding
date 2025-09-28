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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> for specs */
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
{
    /* code modified by LLM (iteration 5): compute rolling maximum using loop with invariants */
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    let n: usize = numbers.len();
    let mut current_max: i8 = 0;

    while i < n
        invariant
            0 <= (i as int) <= (n as int),
            result.len() == i,
            (forall|k: int| 0 <= k < (i as int) ==> result@[k] as int == max_up_to(vec_to_seq_int(numbers), k)),
            (i != 0 ==> current_max as int == max_up_to(vec_to_seq_int(numbers), (i as int) - 1)),
        decreases (n as int) - (i as int)
    {
        let num_i8: i8 = numbers[i];
        if i == 0 {
            current_max = num_i8;
            result.push(num_i8);
        } else {
            if num_i8 > current_max {
                current_max = num_i8;
                result.push(num_i8);
            } else {
                let prev = result[result.len() - 1];
                result.push(prev);
            }
        }
        i += 1;
    }

    result
}
// </vc-code>


}

fn main() {}