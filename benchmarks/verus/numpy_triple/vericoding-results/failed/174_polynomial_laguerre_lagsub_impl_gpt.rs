// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple spec helper to express i8 difference as int */
spec fn diff_i8_as_int(a: i8, b: i8) -> int {
    a as int - b as int
}
// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement lagsub without ghost ints; use i16 intermediate arithmetic and a simple loop */
    let n = c1.len();
    let mut res: Vec<i8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            c1.len() == n,
            c2.len() == n,
        decreases n - i
    {
        let val: i8 = ((c1[i] as i16) - (c2[i] as i16)) as i8;
        res.push(val);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}