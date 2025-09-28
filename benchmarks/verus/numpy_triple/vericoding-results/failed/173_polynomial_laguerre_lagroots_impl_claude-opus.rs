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
{
    /* code modified by LLM (iteration 5): always return single element for c.len() == 2 */
    let n = c.len();
    if n == 2 {
        let mut roots = Vec::new();
        let c0 = c[0];
        let c1 = c[1];
        assert(c1 != 0);  // From precondition
        
        let root_value = 1i8 + c0 / c1;
        roots.push(root_value);
        assert(roots.len() == 1);
        assert(roots@[0] as int == 1 + c@[0] as int / c@[1] as int);
        roots
    } else {
        let roots = Vec::new();
        roots
    }
}
// </vc-code>

}
fn main() {}