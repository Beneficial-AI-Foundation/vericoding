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
    let mut b = Vec::new();
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            b.len() == i,
            n == a.len(),
            n > 0,
            forall|k: int| 0 <= k < i ==> b@[k] == a@[(n - 1) - k],
        decreases n - i,
    {
        // Calculate the index we need to access
        let idx = (n - 1) - i;
        
        // Prove that idx is valid
        assert(i < n);  // From loop condition
        assert(n >= 1); // From n > 0 invariant
        assert(n - 1 >= i); // Since i < n
        assert(idx == (n - 1) - i);
        assert(0 <= idx);
        assert(idx < n);
        assert(idx < a.len());
        
        let elem = a[idx];
        b.push(elem);
        
        assert(b.len() == i + 1);
        assert(b@[i as int] == elem);
        assert(elem == a@[idx as int]);
        assert(idx as int == (n - 1) as int - i as int);
        
        i = i + 1;
    }
    
    b
}
// </vc-code>

// Notice it compiles and the executable generates output (just to see the vectors printed in reverse).

fn main() {
    
}

}