// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_vec_of_len(n: usize) -> (v: Vec<i8>)
    ensures
        v@.len() == n as int,
{
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            v@.len() == i as int,
        decreases n as int - i as int
    {
        v.push(0i8);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn lagcompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut r: usize = 0;
    while r < n - 1
        invariant
            0 <= r as int <= n as int - 1,
            res@.len() == r as int,
            forall|i: int| 0 <= i < res@.len() ==> res@[i].len() == n as int - 1,
        decreases n as int - 1 - r as int
    {
        let row = zero_vec_of_len(n - 1);
        res.push(row);
        r = r + 1;
    }
    proof {
        assert(n as int == c@.len());
    }
    res
}
// </vc-code>

}
fn main() {}