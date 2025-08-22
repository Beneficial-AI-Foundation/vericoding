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
            /* code modified by LLM (iteration 1): added explicit int type annotations to literals */
            result.len() == 2 * i - (if i == 0 { 0int } else { 1int }),
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 0 ==> result[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < result.len() && j % 2 == 1 ==> result[j] == delim
    {
        if i > 0 {
            result.push(delim);
        }
        /* code modified by LLM (iteration 1): removed 'as int' cast which is not allowed in non-ghost code */
        result.push(numbers[i]);
    }
    
    result
}

fn main() {}
}