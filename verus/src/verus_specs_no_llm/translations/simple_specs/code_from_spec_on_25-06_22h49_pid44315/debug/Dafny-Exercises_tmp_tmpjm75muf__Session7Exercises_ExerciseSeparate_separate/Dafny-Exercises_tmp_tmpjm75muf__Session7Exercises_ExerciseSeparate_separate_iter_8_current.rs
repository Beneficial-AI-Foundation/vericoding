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
            // Store the values before swap for proof
            proof {
                let ghost pre_swap = v@;
                let ghost left_val = v@[left as int];
                let ghost right_val = v@[right as int];
            }
            
            // Swap v[left] and v[right]
            let temp = v[left];
            v[left] = v[right];
            v[right] = temp;
            
            // Proof that swap preserves permutation and maintains invariants
            proof {
                // Swap preserves multiset (permutation)
                assert(v@.to_multiset() =~= old(v@).to_multiset());
                assert(isPermutation(v@, old_v));
                
                // After swap, v[left] >= 0, so positive invariant maintained when left increments
                assert(v@[left as int] >= 0);
            }
            
            left += 1;
        }
        right += 1;
    }
    
    // Final assertions to help verification
    proof {
        assert(right == v.len());
        assert(forall|k: int| left <= k < right ==> v@[k] < 0);
        assert(strictNegative(v, left as int, v.len() as int));
    }
    
    left
}

}