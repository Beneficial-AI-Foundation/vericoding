use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    // post-conditions-start
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    
    if numbers.len() == 0 {
        return res;
    }
    
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            i == 0 ==> res.len() == 0,
            i > 0 ==> res.len() == 2 * i - 1,
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> res[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> res[j] == delim,
    {
        if i > 0 {
            res.push(delim);
        }
        res.push(numbers[i as usize]);
        i += 1;
    }
    
    res
}
// </vc-code>

fn main() {}
}