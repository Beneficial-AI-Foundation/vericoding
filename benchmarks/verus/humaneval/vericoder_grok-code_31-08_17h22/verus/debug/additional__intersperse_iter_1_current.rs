use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty or no updates needed
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
    for i in 0..numbers.len() {
        res.push(numbers[i]);
        if i < numbers.len() - 1 {
            res.push(delim);
        }
    }
    res
}
// </vc-code>

fn main() {}
}