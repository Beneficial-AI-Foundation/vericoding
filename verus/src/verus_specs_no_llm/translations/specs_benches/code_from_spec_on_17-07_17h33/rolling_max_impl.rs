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
            /* code modified by LLM (iteration 3): Updated invariant to handle i == 0 case properly */
            i == 0 || current_max == seq_max(numbers@.take(i as int)),
    {
        /* code modified by LLM (iteration 3): Fixed logic to properly compute current_max */
        if i == 0 {
            current_max = numbers[i];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
            // current_max remains the same if numbers[i] <= current_max
        }
        
        result.push(current_max);
        
        /* code modified by LLM (iteration 3): Added lemma call to help prove the assertion */
        proof {
            seq_max_property(numbers@, i as int);
        }
        
        assert(seq_max(numbers@.take((i + 1) as int)) == current_max);
    }
    
    result
}

/* code modified by LLM (iteration 3): Added helper lemma to prove seq_max property */
proof fn seq_max_property(numbers: Seq<i32>, i: int)
    requires 0 <= i < numbers.len(),
    ensures 
        if i == 0 {
            seq_max(numbers.take(i + 1)) == numbers[i]
        } else {
            seq_max(numbers.take(i + 1)) == if numbers[i] > seq_max(numbers.take(i)) {
                numbers[i]
            } else {
                seq_max(numbers.take(i))
            }
        }
{
    if i == 0 {
        assert(numbers.take(1) == seq![numbers[0]]);
    } else {
        assert(numbers.take(i + 1).last() == numbers[i]);
        assert(numbers.take(i + 1).drop_last() == numbers.take(i));
    }
}

fn main() {}
}