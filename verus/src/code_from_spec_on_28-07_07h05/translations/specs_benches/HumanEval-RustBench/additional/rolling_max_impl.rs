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
            /* code modified by LLM (iteration 1): maintain current_max invariant for processed elements */
            i == 0 || current_max == seq_max(numbers@.take(i as int)),
    {
        /* code modified by LLM (iteration 1): update current_max logic to properly maintain invariant */
        if i == 0 {
            current_max = numbers[i];
        } else if numbers[i] > current_max {
            current_max = numbers[i];
        }
        
        /* code modified by LLM (iteration 1): add assertion to help verification */
        assert(current_max == seq_max(numbers@.take((i + 1) as int)));
        
        result.push(current_max);
    }
    
    result
}

fn main() {}
}