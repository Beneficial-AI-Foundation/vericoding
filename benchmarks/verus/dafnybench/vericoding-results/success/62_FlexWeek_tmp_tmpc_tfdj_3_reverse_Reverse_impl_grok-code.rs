use vstd::prelude::*;

verus! {

// Write an *iterative* Verus method reverse with signature:

// <vc-helpers>
// No additional helpers required
// </vc-helpers>

// <vc-spec>
//          fn reverse(a: &Vec<char>) -> Vec<char>

// which takes an input vector of characters 'a' and outputs vector 'b' consisting of
// the elements of the input vector in reverse order. The following conditions apply:
//  - the input vector cannot be empty
//  - the input vector is not modified
//  - you must use iteration
//  - not permitted is an *executable* (parallel) forall statement
//  - not permitted are any other predicates, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires a.len() > 0
    ensures 
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> b[k] == a[(a.len() - 1) - k]
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    for i in 0..a.len() 
        invariant 
            res@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] res@[j] == a@[(a.len() as int - 1) - j]
    {
        res.push(a[a.len() - 1 - i]);
    }
    return res;
}
// </vc-code>

// Notice it compiles and the executable generates output (just to see the vectors printed in reverse).

fn main() {
    
}

}