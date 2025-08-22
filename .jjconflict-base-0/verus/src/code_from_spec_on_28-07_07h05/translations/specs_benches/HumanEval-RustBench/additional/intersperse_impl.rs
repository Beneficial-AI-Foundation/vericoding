/* code modified by LLM (iteration 1): Added explicit int type annotations to resolve type inference error */
use vstd::prelude::*;

verus! {

fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    // post-conditions-start
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
    // post-conditions-end
{
    if numbers.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    
    for i in 0..numbers.len()
        invariant
            result.len() == 2 * i - (if i == 0 { 0int } else { 1int }),
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 0 ==> result[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 1 ==> result[j] == delim
    {
        if i > 0 {
            result.push(delim);
        }
        result.push(numbers[i]);
    }
    
    result
}

fn main() {}
}