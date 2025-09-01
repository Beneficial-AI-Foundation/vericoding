use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if numbers.len() == 0 {
        return Vec::new();
    }
    let mut res = Vec::new();
    let n = numbers.len();
    for i in 0..n {
        res.push(numbers[i]);
        if i != n - 1 {
            res.push(delim);
        }
    }
    proof {
        assert(res@.len() == 2 * (n as int) - 1);
        assert forall |i: int| #![trigger res@[i]] 0 <= i < res@.len() && i % 2 == 0 ==> res@[i] == numbers@[i / 2];
        assert forall |i: int| #![trigger res@[i]] 0 <= i < res@.len() && i % 2 == 1 ==> res@[i] == delim;
    }
    res
}
// </vc-code>

fn main() {}
}