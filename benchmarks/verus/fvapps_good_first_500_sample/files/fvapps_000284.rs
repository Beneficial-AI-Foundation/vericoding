// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_odd_subarrays(arr: Seq<nat>) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let first = arr[0];
        let rest = arr.skip(1);
        let current_odd_count = if first % 2 == 1 { 
            (arr.len() + 1) / 2 
        } else { 
            arr.len() / 2 
        };
        current_odd_count + count_odd_subarrays(rest)
    }
}

fn num_of_subarrays(arr: Vec<nat>) -> (result: nat)
    requires 
        arr.len() > 0,
        arr.len() <= 100000,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] >= 1 && #[trigger] arr[i] <= 100,
    ensures
        result < 1000000007,
        result >= 0,
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
    // let test1 = vec![1, 3, 5];
    // let result1 = num_of_subarrays(test1);
    // assert(result1 == 4);
    
    // let test2 = vec![2, 4, 6];
    // let result2 = num_of_subarrays(test2);
    // assert(result2 == 0);
    
    // let test3 = vec![1, 2, 3, 4, 5, 6, 7];
    // let result3 = num_of_subarrays(test3);
    // assert(result3 == 16);
}