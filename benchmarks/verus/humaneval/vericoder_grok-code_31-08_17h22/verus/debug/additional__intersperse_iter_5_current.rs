use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty
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
    let mut res: Vec<i32> = Vec::new();
    let n = numbers.len();
    for i in 0..n
        invariant
            0 <= i <= n,
            res@.len() == if i == 0 { 0 } else { 2 * (i as int) - 1 },
            forall|k: int| #![trigger] (res@[k]) { 0 <= k < res@.len() && k % 2 == 0 ==> res@[k] == numbers@[k / 2] },
            forall|k: int| #![trigger] (res@[k]) { 0 <= k < res@.len() && k % 2 == 1 ==> res@[k] == delim },
    {
        if i > 0 {
            res.push(delim);
        }
        res.push(numbers[i]);
    }
    res
}
// </vc-code>

fn main() {}
}