use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> i32
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

fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
{
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            /* code modified by LLM (iteration 1): cast i to int for type compatibility */
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
    {
        if i == 0 {
            /* code modified by LLM (iteration 1): cast i to int for indexing */
            current_max = numbers[i as int];
        } else {
            /* code modified by LLM (iteration 1): cast i to int for indexing */
            if numbers[i as int] > current_max {
                current_max = numbers[i as int];
            }
        }
        
        proof {
            /* code modified by LLM (iteration 1): cast i to int for sequence operations */
            assert(numbers@.take(i as int + 1) == numbers@.take(i as int).push(numbers[i as int]));
            assert(seq_max(numbers@.take(i as int + 1)) == 
                if numbers[i as int] > seq_max(numbers@.take(i as int)) {
                    numbers[i as int]
                } else {
                    seq_max(numbers@.take(i as int))
                });
        }
        
        result.push(current_max);
    }
    
    result
}

fn main() {}
}