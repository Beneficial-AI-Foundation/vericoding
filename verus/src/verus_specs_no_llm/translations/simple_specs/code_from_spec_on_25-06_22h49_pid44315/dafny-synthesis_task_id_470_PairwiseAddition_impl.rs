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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(2*j) + a.spec_index(2*j + 1)
    {
        // Prove bounds for array access
        assert(i < a.len());
        assert(a.len() % 2 == 0);
        assert(i % 2 == 0);
        assert(i + 1 < a.len()) by {
            // Since i < a.len() and i % 2 == 0 and a.len() % 2 == 0
            // We know that i is even and less than an even number
            // So i + 1 must be less than a.len()
            assert(i % 2 == 0);
            assert(a.len() % 2 == 0);
            assert(i < a.len());
            // If i + 1 >= a.len(), then i >= a.len() - 1
            // Since a.len() % 2 == 0, we have a.len() >= 0 and a.len() is even
            // Since i % 2 == 0 and i < a.len(), if i == a.len() - 1, then a.len() - 1 would be even
            // But a.len() is even, so a.len() - 1 is odd, contradiction
            // Therefore i <= a.len() - 2, which means i + 1 <= a.len() - 1 < a.len()
            if i + 1 >= a.len() {
                assert(i >= a.len() - 1);
                assert(i == a.len() - 1);  // since i < a.len()
                assert((a.len() - 1) % 2 == 0);  // since i % 2 == 0
                assert(a.len() % 2 == 1);  // contradiction with a.len() % 2 == 0
                assert(false);
            }
        };
        
        let sum = a[i] + a[i + 1];
        result.push(sum);
        
        // Prove loop invariants are maintained
        assert((i + 2) % 2 == 0);
        assert(i + 2 <= a.len());
        
        // Prove the new element satisfies the postcondition
        let new_len = result.len();
        assert(new_len == (i / 2) + 1);
        assert(new_len == (i + 2) / 2);
        
        // The new element is at index new_len - 1
        let new_index = (new_len - 1) as int;
        assert(new_index == (i as int) / 2);
        assert(2 * new_index == i as int);
        assert(2 * new_index + 1 == (i + 1) as int);
        
        // Prove the new element has the correct value
        assert(result.spec_index(new_index) == sum);
        assert(sum == a[i] + a[i + 1]);
        assert(a[i] == a.spec_index(i as int));
        assert(a[i + 1] == a.spec_index((i + 1) as int));
        assert(result.spec_index(new_index) == a.spec_index(2 * new_index) + a.spec_index(2 * new_index + 1));
        
        i = i + 2;
    }
    
    // Final assertions to help prove the postcondition
    assert(i == a.len());
    assert(result.len() == a.len() / 2);
    
    result
}

}