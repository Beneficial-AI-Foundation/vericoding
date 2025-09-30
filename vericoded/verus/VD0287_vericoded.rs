use vstd::prelude::*;

verus! {

// Write an *iterative* Verus method reverse with signature:

// <vc-helpers>

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
    let mut b: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            b.len() == i,
            forall|k: int| 0 <= k < i ==> b[k] == a[(a.len() - 1) - k]
        decreases a.len() - i
    {
        b.push(a[a.len() - 1 - i]);
        i = i + 1;
    }
    
    b
}
// </vc-code>

// Notice it compiles and the executable generates output (just to see the vectors printed in reverse).

fn main() {
    
}

}