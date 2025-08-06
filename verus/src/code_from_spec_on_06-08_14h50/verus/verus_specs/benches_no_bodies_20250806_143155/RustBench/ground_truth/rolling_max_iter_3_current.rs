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
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
    {
        if i == 0 {
            /* code modified by LLM (iteration 2): use usize for vector indexing */
            current_max = numbers[i];
        } else {
            /* code modified by LLM (iteration 2): use usize for vector indexing */
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        result.push(current_max);
        
        proof {
            assert(numbers@.take(i as int + 1).last() == numbers[i as int]);
            assert(numbers@.take(i as int + 1).drop_last() =~~= numbers@.take(i as int));
            
            if i == 0 {
                assert(numbers@.take(1).len() == 1);
                assert(seq_max(numbers@.take(1)) == numbers[0]);
            } else {
                let prev_max = seq_max(numbers@.take(i as int));
                /* code modified by LLM (iteration 2): use int cast only in ghost context */
                if numbers[i as int] > prev_max {
                    assert(seq_max(numbers@.take(i as int + 1)) == numbers[i as int]);
                } else {
                    assert(seq_max(numbers@.take(i as int + 1)) == prev_max);
                }
            }
        }
    }
    
    result
}

fn main() {}
}