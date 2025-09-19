// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn list_maximum(xs: Seq<nat>) -> nat {
    if xs.len() == 0 {
        0
    } else {
        xs.fold_left(0, |acc: nat, x: nat| if x > acc { x } else { acc })
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max_army_strength(n: usize, arr: Vec<nat>) -> (result: nat)
    requires 
        n == arr.len(),
        arr.len() > 0,
    ensures 
        result >= list_maximum(arr@),
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
    // Apps difficulty: interview
    // Assurance level: guarded
    
    // let result1 = find_max_army_strength(3, vec![1, 3, 2]);
    // println!("{}", result1); // Expected: 3
    
    // let result2 = find_max_army_strength(2, vec![1, 2]);
    // println!("{}", result2); // Expected: 2
    
    // let result3 = find_max_army_strength(7, vec![1, 2, 5, 4, 3, 6, 7]);
    // println!("{}", result3); // Expected: 9
}