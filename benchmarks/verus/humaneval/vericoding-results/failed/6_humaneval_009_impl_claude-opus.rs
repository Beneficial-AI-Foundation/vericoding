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
/* helper modified by LLM (iteration 5): Fixed vec_to_seq_int parameter to take reference */
spec fn vec_to_seq_int(v: &Vec<i8>) -> Seq<int> {
    v@.map(|_, x: i8| x as int)
}

proof fn lemma_max_up_to_properties(numbers: Seq<int>, index: int)
    requires
        0 <= index < numbers.len(),
    ensures
        forall|j: int| 0 <= j <= index ==> numbers[j] <= max_up_to(numbers, index),
        exists|j: int| 0 <= j <= index && numbers[j] == max_up_to(numbers, index),
    decreases index
{
    if index == 0 {
        assert(numbers[0] <= max_up_to(numbers, 0));
        assert(numbers[0] == max_up_to(numbers, 0));
    } else {
        lemma_max_up_to_properties(numbers, index - 1);
        let prev_max = max_up_to(numbers, index - 1);
        if numbers[index] > prev_max {
            assert(max_up_to(numbers, index) == numbers[index]);
            assert(forall|j: int| 0 <= j < index ==> numbers[j] <= prev_max);
            assert(prev_max < numbers[index]);
        } else {
            assert(max_up_to(numbers, index) == prev_max);
        }
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
    /* code modified by LLM (iteration 5): Fixed vec_to_seq_int calls to pass reference to numbers */
    let mut result = Vec::new();
    if numbers.len() == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    let mut current_max: i8 = numbers[0];
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result.len() == i,
            i > 0 ==> current_max as int == max_up_to(vec_to_seq_int(&numbers), (i - 1) as int),
            forall|j: int| 0 <= j < i ==> result[j] as int == max_up_to(vec_to_seq_int(&numbers), j),
    {
        if i == 0 {
            current_max = numbers[0];
        } else if numbers[i] > current_max {
            current_max = numbers[i];
        }
        
        result.push(current_max);
        
        proof {
            let nums_seq = vec_to_seq_int(&numbers);
            assert(result[i as int] as int == current_max as int);
            if i == 0 {
                assert(max_up_to(nums_seq, 0) == nums_seq[0]);
                assert(current_max as int == numbers[0] as int);
            } else {
                assert(max_up_to(nums_seq, i as int) == 
                    if nums_seq[i as int] > max_up_to(nums_seq, (i - 1) as int) {
                        nums_seq[i as int]
                    } else {
                        max_up_to(nums_seq, (i - 1) as int)
                    });
            }
            lemma_max_up_to_properties(nums_seq, i as int);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}