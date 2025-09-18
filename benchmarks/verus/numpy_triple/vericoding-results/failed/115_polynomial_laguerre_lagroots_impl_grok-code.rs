// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn compute_root(c0: i32, c1: i32) -> int
requires c1 != 0
ensures result == 1 + c0 as int / c1 as int { 1 + c0 as int / c1 as int }
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
    /* code modified by LLM (iteration 4): Fixed syntax error, used integer division with casting to match spec ensures */
    let mut roots = Vec::new();
    if c.len() == 2 {
        let c0 = c[0];
        let c1 = c[1];
        let c0_int = c0 as int;
        let c1_int = c1 as int;
        proof {
            assert(c1 as int != 0);
            assert(compute_root(c0, c1) == 1 + c0 as int / c1 as int);
        }
        let root_int = 1 + c0_int / c1_int;
        let root = root_int as i32;
        roots.push(root);
    }
    roots
}
// </vc-code>

}
fn main() {}