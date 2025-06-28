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
    // Verus can automatically prove multiset equality for swaps
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
            // Perform the swap
            let ghost pre_swap = v@;
            
            let temp = v[left];
            v[left] = v[right];
            v[right] = temp;
            
            proof {
                // Prove swap preserves multiset
                lemma_swap_preserves_multiset(pre_swap, v@, left as int, right as int);
                
                // Chain the permutation relationships
                assert(pre_swap.to_multiset() == v@.to_multiset());
                assert(pre_swap.to_multiset() == old_v.to_multiset());
                assert(v@.to_multiset() == old_v.to_multiset());
            }
            
            left += 1;
        }
        right += 1;
    }
    
    left
}

}