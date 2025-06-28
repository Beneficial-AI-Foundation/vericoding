use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PairwiseAddition(a: Vec<int>) -> (result: Vec<int>)
    requires
        a.len() % 2 == 0
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(2*i) + a.spec_index(2*i + 1)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(2*j) + a.spec_index(2*j + 1)
    {
        // Establish that i + 1 is within bounds
        assert(i + 1 < a.len()) by {
            // Since i < a.len() (from while condition)
            // and a.len() % 2 == 0 (from precondition)
            // and i % 2 == 0 (from invariant)
            // If i were equal to a.len() - 1, then a.len() - 1 would be even
            // But this would make a.len() odd, contradicting a.len() % 2 == 0
            // Therefore, i <= a.len() - 2, so i + 1 <= a.len() - 1 < a.len()
        };
        
        let sum = a[i] + a[i + 1];
        result.push(sum);
        
        // Help Verus understand the arithmetic
        assert((i + 2) / 2 == i / 2 + 1) by {
            // This follows from i % 2 == 0
        };
        
        // Maintain the forall invariant
        assert(forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(2*j) + a.spec_index(2*j + 1)) by {
            // The new element at index i/2 satisfies the property
            assert(result.spec_index(i / 2) == a.spec_index(2 * (i / 2)) + a.spec_index(2 * (i / 2) + 1));
            assert(2 * (i / 2) == i); // since i % 2 == 0
        };
        
        i += 2;
    }
    
    // Final assertion to help with postcondition
    assert(i == a.len());
    assert(result.len() == a.len() / 2);
    
    result
}

}