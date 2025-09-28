// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed length invariant and added proper bounds checking */
    if numbers.len() == 0 {
        return Vec::new();
    }
    
    let mut res = Vec::new();
    
    for i in 0..numbers.len()
        invariant
            res.len() == if i == 0 { 0 } else { 2 * i - 1 },
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> j / 2 < numbers.len() && res@[j] == numbers@[j / 2],
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> res@[j] == delim
    {
        if i > 0 {
            res.push(delim);
        }
        res.push(numbers[i]);
    }
    
    res
}
// </vc-code>

}
fn main() {}