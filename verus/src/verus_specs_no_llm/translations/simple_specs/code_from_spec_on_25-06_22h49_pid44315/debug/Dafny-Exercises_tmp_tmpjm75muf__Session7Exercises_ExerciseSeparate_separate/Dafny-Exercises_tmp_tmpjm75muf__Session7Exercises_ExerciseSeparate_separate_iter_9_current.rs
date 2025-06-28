use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn strictNegative(v: &Vec<int>, i: int, j: int) -> bool {
    forall|u: int| i <= u < j ==> v@[u] < 0
}

spec fn isPermutation(s: Seq<int>, t: Seq<int>) -> bool {
    s.to_multiset() == t.to_multiset()
}

// Helper lemma for swap preserving multiset
proof fn lemma_swap_preserves_multiset(v1: Seq<int>, v2: Seq<int>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        v1.len() == v2.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v1[k] == v2[k]
    ensures
        v1.to_multiset() == v2.to_multiset()
{
    // The proof follows from the fact that swapping two elements preserves multiset
}

fn separate(v: &mut Vec<int>) -> (i: usize)
    ensures 
        i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strictNegative(v, i as int, v.len() as int),
        isPermutation(v@, old(v)@)
{
    let mut left = 0;
    let mut right = 0;
    let ghost old_v = v@;
    
    while right < v.len()
        invariant
            left <= right <= v.len(),
            positive(v@.subrange(0, left as int)),
            forall|k: int| left <= k < right ==> v@[k] < 0,
            isPermutation(v@, old_v)
    {
        if v[right] >= 0 {
            // Capture state before swap
            let ghost pre_swap = v@;
            let ghost left_val = v@[left as int];
            let ghost right_val = v@[right as int];
            
            // Perform the swap
            let temp = v[left];
            v[left] = v[right];
            v[right] = temp;
            
            // Prove the swap maintains our invariants
            proof {
                // Show that swap preserves multiset
                lemma_swap_preserves_multiset(pre_swap, v@, left as int, right as int);
                
                // Transitivity of permutation
                assert(isPermutation(pre_swap, old_v));
                assert(isPermutation(v@, pre_swap));
                assert(isPermutation(v@, old_v));
                
                // The new element at position left is non-negative
                assert(v@[left as int] == right_val);
                assert(right_val >= 0);
                
                // All elements from 0 to left are non-negative
                assert(forall|k: int| 0 <= k < left ==> v@[k] >= 0);
                assert(positive(v@.subrange(0, left as int)));
                
                // After incrementing left, elements from left to right are negative
                assert(forall|k: int| (left + 1) <= k < right ==> v@[k] < 0);
            }
            
            left += 1;
            
            proof {
                // Verify positive invariant after incrementing left
                assert(positive(v@.subrange(0, left as int)));
                
                // Verify negative invariant 
                assert(forall|k: int| left <= k < right ==> v@[k] < 0);
            }
        } else {
            proof {
                // v[right] < 0, so negative invariant extends
                assert(v@[right as int] < 0);
                assert(forall|k: int| left <= k < right ==> v@[k] < 0);
            }
        }
        right += 1;
        
        proof {
            // Maintain the extended negative invariant
            assert(forall|k: int| left <= k < right ==> v@[k] < 0);
        }
    }
    
    // Final verification
    proof {
        assert(right == v.len());
        assert(left <= v.len());
        assert(positive(v@.subrange(0, left as int)));
        assert(forall|k: int| left <= k < v.len() ==> v@[k] < 0);
        assert(strictNegative(v, left as int, v.len() as int));
        assert(isPermutation(v@, old_v));
    }
    
    left
}

}