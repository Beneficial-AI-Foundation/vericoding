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
                &&& 3*i + 2 < result.len()
                &&& result.spec_index(3*i) == s1.spec_index(i)
                &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                &&& result.spec_index(3*i + 2) == s3.spec_index(i)
            }
    {
        let old_result = result;
        let old_idx = idx;
        
        result = result.push(s1[idx]);
        result = result.push(s2[idx]);
        result = result.push(s3[idx]);
        
        proof {
            // Prove length is correct
            assert(result.len() == old_result.len() + 3);
            assert(old_result.len() == 3 * old_idx);
            assert(result.len() == 3 * old_idx + 3);
            assert(result.len() == 3 * (old_idx + 1));
            
            // Prove new elements are correct
            assert(result.spec_index(3*old_idx) == s1.spec_index(old_idx));
            assert(result.spec_index(3*old_idx + 1) == s2.spec_index(old_idx));
            assert(result.spec_index(3*old_idx + 2) == s3.spec_index(old_idx));
            
            // Key insight: prove that 3*old_idx + 2 < result.len()
            assert(3*old_idx + 2 < result.len());
            
            // Prove old elements are preserved
            assert(forall|j: int| 0 <= j < old_result.len() ==> 
                result.spec_index(j) == old_result.spec_index(j));
            
            // Prove invariant for all previous elements
            assert(forall|i: int| 0 <= i < old_idx ==> {
                &&& 3*i + 2 < old_result.len()
                &&& old_result.spec_index(3*i) == s1.spec_index(i)
                &&& old_result.spec_index(3*i + 1) == s2.spec_index(i)
                &&& old_result.spec_index(3*i + 2) == s3.spec_index(i)
            });
            
            // Show that for previous elements, the bounds still hold in new result
            assert(forall|i: int| 0 <= i < old_idx ==> 3*i + 2 < result.len());
            
            // Combine to show invariant holds for all elements including new one
            assert(forall|i: int| 0 <= i < old_idx + 1 ==> {
                &&& 3*i + 2 < result.len()
                &&& result.spec_index(3*i) == s1.spec_index(i)
                &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                &&& result.spec_index(3*i + 2) == s3.spec_index(i)
            });
        }
        
        idx = idx + 1;
    }
    
    result
}

}