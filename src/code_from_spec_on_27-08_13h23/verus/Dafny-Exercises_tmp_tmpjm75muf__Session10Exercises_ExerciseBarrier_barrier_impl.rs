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
proof fn lemma_all_less(v: Seq<i32>, p: usize)
    requires 
        v.len() > 0,
        p < v.len(),
    ensures
        (forall|k: usize, l: usize| k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int])
        == (forall|k: usize, l: usize| k <= p && l > p && l < v.len() ==> v[k as int] < v[l as int])
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn barrier(v: &[i32], p: usize) -> (b: bool)
    requires 
        v.len() > 0,
        p < v.len(),
    ensures 
        b == (forall|k: usize, l: usize| k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int])
{
    let mut max_left = v[0];
    let mut i = 0;
    
    // Find max in left part (including p)
    while i <= p
        invariant 
            i <= p + 1,
            forall|k: usize| k < i ==> v[k as int] <= max_left,
            exists|k: usize| k < i ==> v[k as int] == max_left,
    {
        if v[i] > max_left {
            max_left = v[i];
        }
        i = i + 1;
    }
    
    // Check if all elements after p are greater than max_left
    i = p + 1;
    while i < v.len()
        invariant 
            p + 1 <= i <= v.len(),
            forall|k: usize| k < p + 1 ==> v[k as int] <= max_left,
            exists|k: usize| k < p + 1 ==> v[k as int] == max_left,
            forall|k: usize| p < k < i ==> v[k as int] > max_left,
    {
        if v[i] <= max_left {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}

}