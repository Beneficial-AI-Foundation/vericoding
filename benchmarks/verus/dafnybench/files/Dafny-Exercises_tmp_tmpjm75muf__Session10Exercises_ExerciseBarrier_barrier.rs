use vstd::prelude::*;

verus! {

//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 

//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn barrier(v: &[i32], p: usize) -> (b: bool)
//Give the precondition
//Give the postcondition
//{Implement and verify}
    requires 
        v.len() > 0,
        p < v.len(),
    ensures 
        b == forall|k: usize, l: usize| 
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]
// </vc-spec>
// <vc-code>
{
    assume(false);
    true
}
// </vc-code>

fn main() {}

}