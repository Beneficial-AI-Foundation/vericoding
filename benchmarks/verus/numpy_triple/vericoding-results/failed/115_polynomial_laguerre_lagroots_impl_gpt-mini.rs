// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that for len==2 the last coefficient is at index 1 and is nonzero */
proof fn last_nonzero_len2(c: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
        c.len() == 2,
    ensures
        c@[1] != 0
{
    assert(c.len() == 2);
    assert(c.len() - 1 == 1);
    assert(c@[c.len() - 1 as int] != 0);
    assert(c@[1] != 0);
}

// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i32>) -> (roots: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] == 1 + c@[0] / c@[1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute root for linear polynomial using sequence indexing and proved nonzero divisor */
    let mut roots: Vec<i32> = Vec::new();
    if c.len() == 2 {
        proof {
            last_nonzero_len2(c);
        }
        let a0: i32 = c@[0];
        let a1: i32 = c@[1];
        proof {
            assert(a1 != 0);
        }
        let r: i32 = 1 + a0 / a1;
        roots.push(r);
    }
    roots
}
// </vc-code>

}
fn main() {}