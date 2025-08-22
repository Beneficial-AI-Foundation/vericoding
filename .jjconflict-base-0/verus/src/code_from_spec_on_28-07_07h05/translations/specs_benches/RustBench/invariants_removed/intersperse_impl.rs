use vstd::prelude::*;

verus! {

fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
{
    if numbers.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    
    for i in 0..numbers.len()
        invariant
            /* code modified by LLM (iteration 4): corrected length invariant to match actual length at loop start */
            result.len() == if i == 0 { 0 } else { 2 * i },
            /* code modified by LLM (iteration 4): maintained element invariants with proper bounds */
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 0 ==> result[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 1 ==> result[j] == delim
    {
        result.push(numbers[i]);
        
        /* code modified by LLM (iteration 4): corrected assertion after first push */
        assert(result.len() == 2 * i + 1);
        
        if i < numbers.len() - 1 {
            result.push(delim);
            /* code modified by LLM (iteration 4): corrected assertion after second push */
            assert(result.len() == 2 * i + 2);
            assert(result.len() == 2 * (i + 1));
        } else {
            /* code modified by LLM (iteration 4): corrected assertion for last iteration case */
            assert(i == numbers.len() - 1);
            assert(result.len() == 2 * i + 1);
            assert(result.len() == 2 * (numbers.len() - 1) + 1);
            assert(result.len() == 2 * numbers.len() - 1);
        }
    }
    
    result
}

fn main() {}
}