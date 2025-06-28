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
    let mut i = a.len();
    
    while i > 0
        invariant
            result.len() + i == a.len(),
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(a.len() - j - 1)
    {
        i = i - 1;
        
        // Add proof annotations to help Verus verify the invariant
        proof {
            assert(i < a.len());
            assert(result.len() == a.len() - i - 1);
        }
        
        result.push(a.spec_index(i as int));
        
        proof {
            let old_result_len = result.len() - 1;
            assert(result.spec_index(old_result_len as int) == a.spec_index(i as int));
            assert(result.len() + i == a.len());
            
            // Verify the invariant holds for the new element
            assert(forall|j: int| 0 <= j < old_result_len ==> 
                result.spec_index(j) == a.spec_index(a.len() - j - 1));
        }
    }
    
    proof {
        assert(i == 0);
        assert(result.len() == a.len());
        assert(forall|j: int| 0 <= j < result.len() ==> 
            result.spec_index(j) == a.spec_index(a.len() - j - 1));
    }
    
    result
}

}