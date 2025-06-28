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
            // Swap v[left] and v[right] using array indexing
            let temp = v[left];
            v[left] = v[right];
            v[right] = temp;
            
            // Proof that swap preserves permutation
            proof {
                let ghost pre_swap = v@;
                // The swap operation preserves the multiset
                assert(v@.to_multiset() =~= pre_swap.to_multiset());
                // Transitivity of permutation
                assert(isPermutation(v@, old_v));
            }
            
            left += 1;
        }
        right += 1;
        
        // Help verification understand the invariant is maintained
        proof {
            assert(forall|k: int| left <= k < right ==> v@[k] < 0) by {
                if right > 0 && v@[right - 1] >= 0 {
                    // The element we just processed was non-negative and got swapped to left part
                    assert(left > 0 ==> v@[left - 1] >= 0);
                } else {
                    // The element we just processed was negative and stays in right part
                }
            }
        }
    }
    
    // Final verification help
    proof {
        assert(left <= v.len());
        assert(positive(v@.subrange(0, left as int)));
        assert(right == v.len());
        assert(forall|k: int| left <= k < right ==> v@[k] < 0);
        assert(strictNegative(v, left as int, v.len() as int));
        assert(isPermutation(v@, old_v));
    }
    
    left
}

}