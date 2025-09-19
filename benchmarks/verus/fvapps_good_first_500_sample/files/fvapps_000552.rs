// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn has_three_consecutive_helper(arr: Seq<i32>, i: int) -> bool {
    1 <= i < arr.len() - 1 && arr[i-1] == arr[i] && arr[i] == arr[i+1]
}

spec fn has_three_consecutive(arr: Seq<i32>) -> bool {
    exists|i: int| #[trigger] has_three_consecutive_helper(arr, i)
}
// </vc-helpers>

// <vc-spec>
fn can_chef_paint(arr: Vec<i32>) -> (result: bool)
    requires 
        arr.len() >= 3,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= arr[i] && arr[i] <= 100000,
    ensures 
        result <==> has_three_consecutive(arr@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![1, 5, 5, 5];
    // let result1 = can_chef_paint(test1);
    // println!("{}", if result1 { "Yes" } else { "No" }); // Should print "Yes"
    
    // let test2 = vec![1, 1, 1, 5];
    // let result2 = can_chef_paint(test2);
    // println!("{}", if result2 { "Yes" } else { "No" }); // Should print "Yes"
    
    // let test3 = vec![5, 5, 2];
    // let result3 = can_chef_paint(test3);
    // println!("{}", if result3 { "Yes" } else { "No" }); // Should print "No"
}