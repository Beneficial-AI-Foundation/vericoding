// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn list_sum(l: Seq<i32>) -> int
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else {
        l[0] + list_sum(l.skip(1))
    }
}

fn min_grass_needed(arr: Vec<i32>) -> (result: nat)
    requires 
        arr.len() > 0,
        list_sum(arr@) == 0,
    ensures result >= 0
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
    // /* Test cases to verify the implementation
    // let test1 = vec![5, -5];
    // let result1 = min_grass_needed(test1);
    // assert(result1 == 5);
    // 
    // let test2 = vec![-5, 5];  
    // let result2 = min_grass_needed(test2);
    // assert(result2 == 5);
    // 
    // let test3 = vec![1, 2, -3];
    // let result3 = min_grass_needed(test3);
    // assert(result3 == 4); */
}