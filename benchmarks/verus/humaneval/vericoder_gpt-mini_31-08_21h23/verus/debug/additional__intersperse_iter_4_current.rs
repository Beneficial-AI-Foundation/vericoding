use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let n: nat = numbers.len();
    if n == 0 {
        return vec![];
    }
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant i < n ==> res.len() == 2 * i;
        invariant i == n ==> res.len() == (if n == 0 { 0 } else { 2 * n - 1 });
        invariant forall |j: nat| j < i ==> res[2 * j] == numbers[j];
        invariant forall |j: nat| j + 1 < i ==> res[2 * j + 1] == delim;
    {
        res.push(numbers[i]);
        if i + 1 < n {
            res.push(delim);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}