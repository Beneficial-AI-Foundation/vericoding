use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}
// pure-end

fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            /* code modified by LLM (iteration 1): updated invariant to correctly track current_max */
            i == 0 || current_max == seq_max(numbers@.take(i as int)),
    {
        /* code modified by LLM (iteration 1): corrected logic to always compute max between current element and previous max */
        if i == 0 {
            current_max = numbers[i];
        } else if numbers[i] > current_max {
            current_max = numbers[i];
        }
        result.push(current_max);
        
        /* code modified by LLM (iteration 1): added lemma call and proof to establish the assertion */
        proof {
            assert(numbers@.take((i + 1) as int).last() == numbers[i as int]);
            if i == 0 {
                assert(seq_max(numbers@.take(1)) == numbers[0]);
            } else {
                assert(numbers@.take((i + 1) as int) == numbers@.take(i as int).push(numbers[i as int]));
                if numbers[i] > seq_max(numbers@.take(i as int)) {
                    assert(seq_max(numbers@.take((i + 1) as int)) == numbers[i]);
                } else {
                    assert(seq_max(numbers@.take((i + 1) as int)) == seq_max(numbers@.take(i as int)));
                }
            }
            assert(current_max == seq_max(numbers@.take((i + 1) as int)));
        }
    }
    
    result
}

}
fn main() {}