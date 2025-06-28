use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove transitivity
proof fn lemma_transitivity(a: Vec<int>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
        forall|k: int| 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1)
    ensures
        a.spec_index(i) <= a.spec_index(j)
    decreases j - i
{
    if i + 1 == j {
        // Base case: adjacent elements
        assert(a.spec_index(i) <= a.spec_index(i + 1));
    } else {
        // Recursive case: use transitivity
        lemma_transitivity(a, i, j - 1);
        assert(a.spec_index(i) <= a.spec_index(j - 1));
        assert(a.spec_index(j - 1) <= a.spec_index(j));
    }
}

fn IsSorted(a: Vec<int>) -> (sorted: bool)
    requires
        a.len() > 0
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a.spec_index(i) > a.spec_index(j)
{
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|k: int| 0 <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1),
            forall|p: int, q: int| 0 <= p < q <= i ==> a.spec_index(p) <= a.spec_index(q)
    {
        if a[i] > a[i + 1] {
            assert(a.spec_index(i) > a.spec_index(i + 1));
            assert(0 <= i < i + 1 < a.len());
            return false;
        }
        
        // Prove the extended transitivity before incrementing i
        let old_i = i;
        
        // Prove that all elements from 0 to i are <= a[i+1]
        proof {
            let mut p = 0;
            while p <= old_i
                invariant
                    0 <= p <= old_i + 1,
                    forall|q: int| 0 <= q < p ==> a.spec_index(q) <= a.spec_index(old_i + 1)
            {
                if p < old_i {
                    // Use existing transitivity from loop invariant
                    assert(a.spec_index(p) <= a.spec_index(old_i));
                    assert(a.spec_index(old_i) <= a.spec_index(old_i + 1));
                } else if p == old_i {
                    // Direct from the condition we just checked
                    assert(a.spec_index(old_i) <= a.spec_index(old_i + 1));
                }
                p = p + 1;
            }
        }
        
        i = i + 1;
    }
    
    // At this point, we know all adjacent elements are in order
    assert(forall|k: int| 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
    
    // Use the helper lemma to prove full transitivity
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
            let i_witness = choose|i: int, j: int| 0 <= i < j < a.len();
            if exists|i: int, j: int| 0 <= i < j < a.len() {
                let (i_val, j_val) = i_witness;
                lemma_transitivity(a, i_val, j_val);
            }
        };
    }
    
    return true;
}

}