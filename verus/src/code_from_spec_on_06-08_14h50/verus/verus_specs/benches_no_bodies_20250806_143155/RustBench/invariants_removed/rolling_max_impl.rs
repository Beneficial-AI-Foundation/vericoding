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
            /* code modified by LLM (iteration 1): use ghost variable for int operations */
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
    {
        if i == 0 {
            /* code modified by LLM (iteration 1): use usize indexing directly */
            current_max = numbers[i];
        } else {
            /* code modified by LLM (iteration 1): use usize indexing directly */
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        proof {
            /* code modified by LLM (iteration 1): use ghost operations for sequence manipulation */
            let ghost_i: int = i as int;
            assert(numbers@.take(ghost_i + 1) == numbers@.take(ghost_i).push(numbers[ghost_i]));
            assert(seq_max(numbers@.take(ghost_i + 1)) == 
                if numbers[ghost_i] > seq_max(numbers@.take(ghost_i)) {
                    numbers[ghost_i]
                } else {
                    seq_max(numbers@.take(ghost_i))
                });
        }
        
        result.push(current_max);
    }
    
    result
}

fn main() {}
}