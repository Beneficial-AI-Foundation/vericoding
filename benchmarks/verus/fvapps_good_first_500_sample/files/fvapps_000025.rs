// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_triangle(x: nat, y: nat, z: nat) -> bool {
    x > 0 && y > 0 && z > 0
}

fn polygon_cut(n: nat, triangles: Vec<(nat, nat, nat)>) -> (result: (Vec<nat>, Vec<nat>))
    requires 
        n >= 3,
        triangles.len() == n - 2,
    ensures
        result.0.len() == n,
        result.1.len() == n - 2,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] >= 1 && result.0[i] <= n,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] >= 1 && result.1[i] <= (triangles.len() as int),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

}

fn main() {
    // let n1 = 6;
    // let vertices1 = vec![1, 6, 4, 2, 5, 3];
    // let cuts1 = vec![4, 2, 3, 1];
    
    // let n2 = 6; 
    // let vertices2 = vec![1, 4, 2, 6, 5, 3];
    // let cuts2 = vec![3, 4, 2, 1];
    
    // println!("n1: {}", n1);
    // println!("vertices1 length: {}", vertices1.len());
    // println!("cuts1 length: {}", cuts1.len());
    
    // println!("n2: {}", n2);
    // println!("vertices2 length: {}", vertices2.len()); 
    // println!("cuts2 length: {}", cuts2.len());
}