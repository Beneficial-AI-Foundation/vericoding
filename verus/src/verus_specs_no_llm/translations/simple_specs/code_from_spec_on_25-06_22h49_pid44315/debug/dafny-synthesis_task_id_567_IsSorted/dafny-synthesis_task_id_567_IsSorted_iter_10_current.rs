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
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|k: int| 0 <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1),
            forall|p: int, q: int| 0 <= p < q <= i ==> a.spec_index(p) <= a.spec_index(q)
    {
        if a[i] > a[i + 1] {
            assert(a.spec_index(i as int) > a.spec_index((i + 1) as int));
            assert(0 <= i as int < (i + 1) as int < a.len());
            return false;
        }
        
        // Prove that the new adjacent pair is sorted
        assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int));
        
        // Prove transitivity for all pairs involving the new element
        assert(forall|p: int, q: int| 0 <= p < q <= (i + 1) as int ==> a.spec_index(p) <= a.spec_index(q)) by {
            forall|p: int, q: int| 0 <= p < q <= (i + 1) as int implies a.spec_index(p) <= a.spec_index(q) by {
                if q <= i as int {
                    // Both in previously verified range - already established by invariant
                } else {
                    // q == (i + 1) as int, so we need to show a[p] <= a[i+1]
                    assert(q == (i + 1) as int);
                    if p == i as int {
                        // Direct adjacent case we just verified
                    } else {
                        // p < i, so use transitivity: a[p] <= a[i] <= a[i+1]
                        assert(p < i as int);
                        assert(a.spec_index(p) <= a.spec_index(i as int)); // from invariant
                        assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int)); // just verified
                    }
                }
            }
        };
        
        i = i + 1;
    }
    
    // At this point, we know all adjacent elements are in order
    assert(forall|k: int| 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
    
    // Use the helper lemma to prove full transitivity
    assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
        forall|i: int, j: int| 0 <= i < j < a.len() implies a.spec_index(i) <= a.spec_index(j) by {
            lemma_transitivity(a, i, j);
        }
    };
    
    return true;
}

}