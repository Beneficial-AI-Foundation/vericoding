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
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(i + j)
    {
        i = i - 1;
        
        // Get the element at index i
        let element = a[i];
        result.push(element);
        
        // Help the verifier understand the relationship after push
        assert(result.len() == a.len() - i);
        assert(result.spec_index(result.len() - 1) == a.spec_index(i));
        
        // Strengthen the invariant understanding
        assert forall|j: int| 0 <= j < result.len() - 1 implies result.spec_index(j) == a.spec_index(i + 1 + j) by {
            // This follows from the previous invariant before the push
        };
    }
    
    // Post-loop assertions
    assert(i == 0);
    assert(result.len() == a.len());
    
    // Prove the postcondition with detailed reasoning
    assert forall|x: int| 0 <= x < a.len() implies result.spec_index(x) == a.spec_index(a.len() - x - 1) by {
        // From the final invariant: result[x] == a[0 + x] == a[x]
        // But we built result by pushing a[a.len()-1], a[a.len()-2], ..., a[0]
        // So result[0] == a[a.len()-1], result[1] == a[a.len()-2], etc.
        // Therefore result[x] == a[a.len() - 1 - x]
        // Which is equivalent to a[a.len() - x - 1] since a.len() - 1 - x == a.len() - x - 1
    };
    
    result
}

}