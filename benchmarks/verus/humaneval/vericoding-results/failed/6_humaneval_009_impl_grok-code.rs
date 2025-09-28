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
/* code modified by LLM (iteration 5): Fixed type mismatches by casting usize indices to int for sequence operations */
{
    if numbers.len() == 0 {
        return Vec::new();
    }
    let mut result = Vec::new();
    let mut current_max = numbers[0];
    let mut max_index = 0;
    result.push(current_max);
    let mut i = 1;
    proof {
        assert(current_max as int == max_up_to(vec_to_seq_int(numbers), 0));
        assert(current_max as int == numbers@[(max_index as int)] as int);
    }
    while i < numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result@[j] as int == max_up_to(vec_to_seq_int(numbers), j),
            current_max as int == max_up_to(vec_to_seq_int(numbers), (i - 1) as int),
            0 <= max_index as int <= (i - 1) as int,
            current_max as int == numbers@[(max_index as int)] as int,
        decreases numbers.len() - i
    {
        if numbers[i] > current_max {
            current_max = numbers[i];
            max_index = i;
        }
        result.push(current_max);
        proof {
            assert(current_max as int == max_up_to(vec_to_seq_int(numbers), i as int));
            assert(current_max as int == numbers@[(max_index as int)] as int);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}