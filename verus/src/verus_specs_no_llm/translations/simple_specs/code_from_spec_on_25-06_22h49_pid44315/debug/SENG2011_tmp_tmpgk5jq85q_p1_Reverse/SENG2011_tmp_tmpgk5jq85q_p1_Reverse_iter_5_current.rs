use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall|x: int| 0 <= x < a.len() ==> b.spec_index(x) == a.spec_index(a.len() - x - 1)
{
    let mut result = Vec::new();
    let mut i: usize = a.len();
    
    while i > 0
        invariant
            result.len() + i == a.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(a.len() - 1 - j)
    {
        i = i - 1;
        
        // Get the element at index i
        let element = a[i];
        result.push(element);
        
        // Help the verifier understand the relationship
        assert(result.len() == a.len() - i);
        assert(result.spec_index(result.len() - 1) == a.spec_index(i));
    }
    
    // Post-loop assertions to help verification
    assert(i == 0);
    assert(result.len() == a.len());
    
    // Prove the postcondition
    assert forall|x: int| 0 <= x < a.len() implies result.spec_index(x) == a.spec_index(a.len() - x - 1) by {
        // The invariant tells us that result[j] == a[a.len() - 1 - j]
        // We want to show result[x] == a[a.len() - x - 1]
        // These are the same when j = x
    };
    
    result
}

}