use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a == old(a),
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b.spec_index(i) == a.spec_index(a.len() - i - 1)
{
    let mut b = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            b.len() == i,
            forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - 1 - k),
            a.len() > 0
    {
        // Calculate the index we're taking from 'a'
        let src_index = a.len() - 1 - i;
        
        // Add proof assertion to help with bounds checking
        assert(0 <= src_index < a.len());
        
        b.push(a[src_index]);
        i = i + 1;
    }
    
    // The loop invariant at exit gives us what we need for the postcondition
    // When i == a.len(), we have:
    // forall|k: int| 0 <= k < a.len() ==> b.spec_index(k) == a.spec_index(a.len() - 1 - k)
    // This is exactly the postcondition since a.len() - 1 - k == a.len() - k - 1
    assert forall|j: int| 0 <= j < a.len() implies b.spec_index(j) == a.spec_index(a.len() - j - 1) by {
        // The loop invariant at exit (when i == a.len()) tells us:
        // b.spec_index(j) == a.spec_index(a.len() - 1 - j)
        // And a.len() - 1 - j == a.len() - j - 1
        assert(a.len() - 1 - j == a.len() - j - 1);
    };
    
    b
}

}