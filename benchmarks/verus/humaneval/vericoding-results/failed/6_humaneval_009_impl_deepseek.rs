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
    v@.map(|i: int, x: i8| x as int)
}

spec fn max_up_to_invariant(numbers: Seq<int>, index: int, current_max: int) -> bool {
    current_max == max_up_to(numbers, index)
}

proof fn max_up_to_monotonic(numbers: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < numbers.len(),
    ensures
        max_up_to(numbers, i) <= max_up_to(numbers, j),
{
    if i < j {
        max_up_to_monotonic(numbers, i, j - 1);
        assert(max_up_to(numbers, j - 1) <= max_up_to(numbers, j));
    }
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
    /* code modified by LLM (iteration 5): Fixed vec_to_seq_int parameter format and maintained loop invariants with correct syntax */
    let mut result = Vec::new();
    let mut current_max: i8 = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            i > 0 ==> current_max as int == max_up_to(vec_to_seq_int(numbers), (i - 1) as int),
            forall|k: int| 0 <= k < i ==> result@[k] as int == max_up_to(vec_to_seq_int(numbers), k),
    {
        if i == 0 {
            current_max = numbers[i];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        result.push(current_max);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}