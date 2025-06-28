use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires
        s1.len() == s2.len() && s2.len() == s3.len()
    ensures
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r.spec_index(3*i) == s1.spec_index(i) && r.spec_index(3*i + 1) == s2.spec_index(i) && r.spec_index(3*i + 2) == s3.spec_index(i)
{
    let mut result = Seq::<int>::empty();
    let mut idx = 0;
    
    while idx < s1.len()
        invariant
            s1.len() == s2.len() && s2.len() == s3.len(),
            0 <= idx <= s1.len(),
            result.len() == 3 * idx,
            forall|i: int| 0 <= i < idx ==> {
                &&& 3*i < result.len()
                &&& 3*i + 1 < result.len()
                &&& 3*i + 2 < result.len()
                &&& result.spec_index(3*i) == s1.spec_index(i)
                &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                &&& result.spec_index(3*i + 2) == s3.spec_index(i)
            }
    {
        // Use spec_index instead of [] for sequence access
        result = result.push(s1.spec_index(idx));
        result = result.push(s2.spec_index(idx));
        result = result.push(s3.spec_index(idx));
        
        proof {
            // Prove length property holds
            assert(result.len() == 3 * (idx + 1));
            
            // Prove properties of the three newly added elements
            let old_len = 3 * idx;
            assert(result.spec_index(old_len) == s1.spec_index(idx));
            assert(result.spec_index(old_len + 1) == s2.spec_index(idx));
            assert(result.spec_index(old_len + 2) == s3.spec_index(idx));
            
            // Help Verus understand the invariant is preserved
            assert(forall|i: int| 0 <= i < idx + 1 ==> {
                if i < idx {
                    // Previous elements are preserved by push operation
                    &&& 3*i < result.len()
                    &&& 3*i + 1 < result.len()
                    &&& 3*i + 2 < result.len()
                    &&& result.spec_index(3*i) == s1.spec_index(i)
                    &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                    &&& result.spec_index(3*i + 2) == s3.spec_index(i)
                } else {
                    // i == idx, these are the newly added elements
                    &&& 3*i < result.len()
                    &&& 3*i + 1 < result.len()
                    &&& 3*i + 2 < result.len()
                    &&& result.spec_index(3*i) == s1.spec_index(i)
                    &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                    &&& result.spec_index(3*i + 2) == s3.spec_index(i)
                }
            });
        }
        
        idx = idx + 1;
    }
    
    result
}

}