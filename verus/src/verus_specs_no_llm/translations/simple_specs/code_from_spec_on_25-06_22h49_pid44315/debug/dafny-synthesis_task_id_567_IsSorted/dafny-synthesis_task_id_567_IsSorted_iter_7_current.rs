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
            assert(a.spec_index(i as int) > a.spec_index((i + 1) as int));
            assert(0 <= i < i + 1 < a.len());
            return false;
        }
        
        // Strengthen the invariant for the next iteration
        assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int));
        
        // Prove transitivity extension
        assert(forall|p: int| 0 <= p <= i ==> a.spec_index(p) <= a.spec_index((i + 1) as int)) by {
            if forall|p: int| 0 <= p <= i {
                let p = choose|p: int| 0 <= p <= i;
                if p < i {
                    assert(a.spec_index(p) <= a.spec_index(i as int));
                    assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int));
                } else if p == i {
                    assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int));
                }
            }
        }
        
        i = i + 1;
    }
    
    // At this point, we know all adjacent elements are in order
    assert(forall|k: int| 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
    
    // Use the helper lemma to prove full transitivity
    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
        if forall|i: int, j: int| 0 <= i < j < a.len() {
            let i_val = choose|i: int, j: int| 0 <= i < j < a.len();
            let j_val = choose|j: int| 0 <= i_val < j < a.len();
            lemma_transitivity(a, i_val, j_val);
        }
    }
    
    return true;
}

}