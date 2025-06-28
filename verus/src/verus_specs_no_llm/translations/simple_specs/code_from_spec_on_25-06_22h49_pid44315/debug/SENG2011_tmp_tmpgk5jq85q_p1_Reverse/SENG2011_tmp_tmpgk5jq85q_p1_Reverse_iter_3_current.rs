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
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(a.len() - j - 1)
    {
        i = i - 1;
        
        // Get the element at index i
        let element = a[i];
        result.push(element);
        
        proof {
            // Help Verus understand the relationship between indices
            assert(i < a.len());
            assert(result.len() == a.len() - i);
            assert(result.spec_index((result.len() - 1) as int) == a.spec_index(i as int));
            
            // The invariant should hold after the push
            assert(forall|j: int| 0 <= j < result.len() ==> 
                result.spec_index(j) == a.spec_index(a.len() - j - 1)) by {
                // For the newly added element
                let new_idx = (result.len() - 1) as int;
                assert(result.spec_index(new_idx) == a.spec_index(i as int));
                assert(i as int == a.len() - new_idx - 1);
                
                // For existing elements, the property is preserved
                assert(forall|j: int| 0 <= j < new_idx ==> 
                    result.spec_index(j) == a.spec_index(a.len() - j - 1));
            };
        }
    }
    
    proof {
        assert(i == 0);
        assert(result.len() == a.len());
    }
    
    result
}

}