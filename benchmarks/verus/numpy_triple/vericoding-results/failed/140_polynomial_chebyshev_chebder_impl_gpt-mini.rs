// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove int to i8 cast roundtrip for 0..127 */
proof fn int_to_i8_roundtrip(i: int)
    requires
        0 <= i,
        i <= 127,
    ensures
        (i as i8) as int == i,
    decreases
        0usize
{
    assert((i as i8) as int == i);
}
// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j as int] == scl * (2 * ((j + 1) as i8)) * c[(j + 1) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and explicit integer suffixes */
    let mut res: Vec<i8> = Vec::new();
    let n: usize = c.len();
    let mut i: usize = 0usize;
    while i < n - 1
        invariant
            res.len() == i,
        decreases
            n - 1 - i
    {
        let val: i8;
        if i == 0usize {
            val = scl * c[1usize];
        } else if i == 1usize {
            val = scl * 4i8 * c[2usize];
        } else {
            let idx = i + 1usize;
            let k = idx as i8;
            val = scl * 2i8 * k * c[idx];
        }
        res.push(val);
        i = i + 1usize;
    }
    res
}
// </vc-code>

}
fn main() {}