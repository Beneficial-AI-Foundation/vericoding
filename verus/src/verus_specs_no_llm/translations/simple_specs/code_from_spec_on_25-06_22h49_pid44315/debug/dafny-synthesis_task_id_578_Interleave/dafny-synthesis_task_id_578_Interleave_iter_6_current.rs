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
        proof {
            // Establish bounds for accessing sequences
            assert(0 <= idx < s1.len());
            assert(0 <= idx < s2.len());
            assert(0 <= idx < s3.len());
        }
        
        result = result.push(s1[idx]);
        result = result.push(s2[idx]);
        result = result.push(s3[idx]);
        
        proof {
            let old_len = 3 * idx;
            let new_len = 3 * (idx + 1);
            
            // Prove length properties
            assert(result.len() == old_len + 3);
            assert(result.len() == new_len);
            
            // Prove the new elements are correct
            assert(result.spec_index(3*idx) == s1.spec_index(idx));
            assert(result.spec_index(3*idx + 1) == s2.spec_index(idx));
            assert(result.spec_index(3*idx + 2) == s3.spec_index(idx));
            
            // Prove bounds for the new elements
            assert(3*idx < result.len());
            assert(3*idx + 1 < result.len());
            assert(3*idx + 2 < result.len());
            
            // Prove that old elements are preserved
            assert(forall|j: int| 0 <= j < old_len ==> 
                result.spec_index(j) == result.drop_last().drop_last().drop_last().spec_index(j));
            
            // Use properties of push to establish preservation
            let temp1 = result.drop_last().drop_last(); // after first push only
            let temp2 = result.drop_last(); // after first two pushes
            
            // Prove invariant for all i including the new one
            assert(forall|i: int| 0 <= i < idx + 1 ==> {
                &&& 3*i + 2 < result.len()
                &&& result.spec_index(3*i) == s1.spec_index(i)
                &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                &&& result.spec_index(3*i + 2) == s3.spec_index(i)
            }) by {
                // For the new element (i == idx)
                if idx < s1.len() {
                    assert(result.spec_index(3*idx) == s1.spec_index(idx));
                    assert(result.spec_index(3*idx + 1) == s2.spec_index(idx));
                    assert(result.spec_index(3*idx + 2) == s3.spec_index(idx));
                }
                
                // For old elements (i < idx), they are preserved by push operations
                assert(forall|i: int| 0 <= i < idx ==> {
                    &&& 3*i + 2 < old_len
                    &&& 3*i + 2 < result.len()
                    &&& result.spec_index(3*i) == s1.spec_index(i)
                    &&& result.spec_index(3*i + 1) == s2.spec_index(i)
                    &&& result.spec_index(3*i + 2) == s3.spec_index(i)
                });
            };
        }
        
        idx = idx + 1;
    }
    
    result
}

}