// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by removing semicolon from requires clause */
fn lagroots_helper1(c: &Vec<i32>, i: int) -> (root: i32)
    requires
        i >= 0 && i < c.len() - 1,
        c@[c.len() - 1] != 0
    ensures
        root == 1 + c@[i] / c@[c.len() - 1]
{
    1 + c[i as usize] / c[c.len() - 1]
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
/* code modified by LLM (iteration 5): Fixed compilation error by removing semicolon from invariant clause */
{
    let mut roots = Vec::new();
    let n = c.len();
    
    if n == 2 {
        let root = 1 + c[0] / c[1];
        roots.push(root);
    } else if n > 2 {
        let mut i: usize = 0;
        while i < n - 1 {
            invariant
                i as int <= (n - 1) as int,
                roots.len() == i,
                forall |j: int| 0 <= j && j < i as int ==> roots@[j] == 1 + c@[j] / c@[n - 1]
            {
                let root = lagroots_helper1(&c, i as int);
                roots.push(root);
                i += 1;
            }
        }
    }
    
    roots
}
// </vc-code>

}
fn main() {}