// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Added proof for division precondition and overflow check */
    let n = c.len();
    if n == 2 {
        proof {
            assert(c@.len() == 2);
            assert(c@[c@.len() - 1] != 0);
            assert(c@[1] != 0);
        }
        
        // Division requires c[1] != 0
        assert(c[1] != 0);
        let div_result: i32 = c[0] / c[1];
        
        // Check for overflow before adding 1
        assert(div_result <= i32::MAX - 1);
        let root: i32 = div_result + 1;
        
        let mut roots = Vec::new();
        roots.push(root);
        
        proof {
            assert(roots@.len() == 1);
            assert(roots@[0] == root);
            assert(root == div_result + 1);
            assert(div_result == c@[0] / c@[1]);
            assert(roots@[0] == 1 + c@[0] / c@[1]);
        }
        
        roots
    } else {
        let roots = Vec::new();
        roots
    }
}
// </vc-code>

}
fn main() {}