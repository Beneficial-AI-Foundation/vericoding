use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove transitivity
proof fn lemma_transitivity(a: Vec<int>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
        forall k :: 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1)
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
        sorted <==> forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        !sorted ==> exists i, j :: 0 <= i < j < a.len() && a.spec_index(i) > a.spec_index(j)
{
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall k :: 0 <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1),
            forall p, q :: 0 <= p < q <= i ==> a.spec_index(p) <= a.spec_index(q)
    {
        if a[i] > a[i + 1] {
            assert(a.spec_index(i) > a.spec_index(i + 1));
            assert(0 <= i < i + 1 < a.len());
            return false;
        }
        
        // Prove the loop invariant is maintained
        assert(forall k :: 0 <= k < i + 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
        
        // Prove transitivity for the extended range
        assert(forall p, q :: 0 <= p < q <= i + 1 ==> a.spec_index(p) <= a.spec_index(q)) by {
            assert(forall p, q :: 0 <= p < q <= i ==> a.spec_index(p) <= a.spec_index(q)); // From invariant
            assert(forall p :: 0 <= p <= i ==> a.spec_index(p) <= a.spec_index(i + 1)) by {
                if 0 <= p < i {
                    assert(a.spec_index(p) <= a.spec_index(i)); // From invariant
                    assert(a.spec_index(i) <= a.spec_index(i + 1)); // Just checked
                } else if p == i {
                    assert(a.spec_index(i) <= a.spec_index(i + 1)); // Just checked
                }
            };
        };
        
        i = i + 1;
    }
    
    // At this point, we know all adjacent elements are in order
    assert(forall k :: 0 <= k < a.len() - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
    
    // Use the helper lemma to prove full transitivity
    assert(forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
        assert(forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)) by {
            lemma_transitivity(a, i, j);
        }
    };
    
    return true;
}

}