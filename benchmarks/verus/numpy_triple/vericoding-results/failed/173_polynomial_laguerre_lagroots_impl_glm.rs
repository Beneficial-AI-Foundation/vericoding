// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i8>) -> (roots: Vec<i8>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] as int == 1 + c@[0] as int / c@[1] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed use of int in non-ghost code by using i32 for intermediate computation */
{
    if c.len() == 2 {
        // Use i32 to avoid overflow in intermediate steps and then cast to i8
        let root = (1 + (c[0] as i32 / c[1] as i32)) as i8;
        vec![root]
    } else {
        vec![]
    }
}
// </vc-code>

}
fn main() {}