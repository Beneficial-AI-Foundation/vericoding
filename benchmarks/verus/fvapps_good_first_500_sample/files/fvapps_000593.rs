// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn check_social_distancing(n: usize, arr: Vec<usize>) -> (result: bool)
    requires 
        n >= 1 && n <= 100,
        arr.len() == n,
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] == 0 || arr[i] == 1),
    ensures
        result == (forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr.len() && i < j && 
            arr[i] == 1 && arr[j] == 1 ==> j - i >= 6),
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
    // let result1 = check_social_distancing(3, vec![1, 0, 1]);
    // println!("{}", if result1 { "YES" } else { "NO" }); // Should print "NO"
    
    // let result2 = check_social_distancing(7, vec![1, 0, 0, 0, 0, 0, 1]);
    // println!("{}", if result2 { "YES" } else { "NO" }); // Should print "YES"
    
    // let result3 = check_social_distancing(11, vec![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1]);
    // println!("{}", if result3 { "YES" } else { "NO" }); // Should print "NO"
}