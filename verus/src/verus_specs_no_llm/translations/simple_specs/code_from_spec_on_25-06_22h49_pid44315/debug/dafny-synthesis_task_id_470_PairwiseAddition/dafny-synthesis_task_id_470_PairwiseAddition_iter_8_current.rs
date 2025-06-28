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
        // Since i < a.len() and a.len() is even and i is even, we know i+1 < a.len()
        assert(i + 1 < a.len());
        
        let sum = a[i] + a[i + 1];
        result.push(sum);
        
        // Help Verus understand the arithmetic and maintain invariants
        assert((i + 2) % 2 == 0);
        assert(i + 2 <= a.len());
        
        // Help Verus understand the relationship between old and new result length
        let old_result_len = result.len();
        assert(old_result_len == (i / 2) + 1);
        assert(old_result_len == (i + 2) / 2);
        
        // Help Verus understand that the new element satisfies the postcondition
        assert(result.spec_index((old_result_len - 1) as int) == a.spec_index(i as int) + a.spec_index((i + 1) as int));
        assert(result.spec_index((old_result_len - 1) as int) == a.spec_index(2 * ((old_result_len - 1) as int)) + a.spec_index(2 * ((old_result_len - 1) as int) + 1));
        
        i = i + 2;
    }
    
    // Final assertions to help prove the postcondition
    assert(i == a.len());
    assert(result.len() == a.len() / 2);
    
    result
}

}