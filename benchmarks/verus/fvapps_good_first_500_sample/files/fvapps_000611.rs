// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn list_max(l: Seq<nat>) -> nat 
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        let rest_max = list_max(l.skip(1));
        if l[0] > rest_max { l[0] } else { rest_max }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_magic_potions(R: nat, G: nat, B: nat, M: nat, r: Vec<nat>, g: Vec<nat>, b: Vec<nat>) -> (result: nat)
    requires 
        R > 0,
        G > 0,
        B > 0,
        r.len() == R,
        g.len() == G,
        b.len() == B,
        forall|x: nat| r@.contains(x) || g@.contains(x) || b@.contains(x) ==> x > 0,
    ensures
        result >= 0,
        result <= {
            let max_r = list_max(r@);
            let max_g = list_max(g@);
            let max_b = list_max(b@);
            if max_r >= max_g && max_r >= max_b { max_r }
            else if max_g >= max_b { max_g }
            else { max_b }
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result1 = solve_magic_potions(1, 1, 1, 1, vec![1], vec![2], vec![3]);
    // println!("Result 1: {}", result1);
    
    // let result2 = solve_magic_potions(1, 1, 1, 1, vec![2], vec![4], vec![6]);
    // println!("Result 2: {}", result2);
    
    // let result3 = solve_magic_potions(3, 2, 2, 2, vec![1, 2, 3], vec![2, 4], vec![6, 8]);
    // println!("Result 3: {}", result3);
}