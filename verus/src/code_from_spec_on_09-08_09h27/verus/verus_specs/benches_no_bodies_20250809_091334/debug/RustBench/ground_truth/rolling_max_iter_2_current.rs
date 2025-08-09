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
    
    let mut j = 0;
    while j < numbers.len()
        invariant
            result.len() == j,
            j <= numbers.len(),
            forall|i: int| 0 <= i < j ==> result[i] == seq_max(numbers@.take(i + 1)),
    {
        if j == 0 {
            current_max = numbers[j];
        } else {
            if numbers[j] > current_max {
                current_max = numbers[j];
            }
        }
        result.push(current_max);
        
        assert(current_max == seq_max(numbers@.take(j + 1))) by {
            if j == 0 {
                /* code modified by LLM (iteration 1): fixed seq macro call syntax */
                assert(numbers@.take(1) == seq![numbers[0]]);
                assert(seq_max(seq![numbers[0]]) == numbers[0]);
            } else {
                assert(numbers@.take(j + 1) == numbers@.take(j).push(numbers[j]));
                assert(numbers@.take(j + 1).drop_last() == numbers@.take(j));
                assert(numbers@.take(j + 1).last() == numbers[j]);
            }
        };
        
        j += 1;
    }
    
    result
}

fn main() {}
}