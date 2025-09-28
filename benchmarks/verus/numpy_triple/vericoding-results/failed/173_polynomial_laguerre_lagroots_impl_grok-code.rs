// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no modification, remained empty */
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
/* code modified by LLM (iteration 3): fixed syntax, logic for c.len() == 2, added proof assert for divider non-zero */
{
    let mut roots = Vec::new();
    if c.len() == 2 {
        proof {
            assert(c@[1] != 0);
        }
        let root_val = (1 as int) + (c@[0] as int) / (c@[1] as int);
        let root = root_val as i8;
        roots.push(root);
    }
    roots
}
// </vc-code>

}
fn main() {}