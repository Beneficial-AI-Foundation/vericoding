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
        
        // Strengthen the invariant for the next iteration
        assert(a.spec_index(i as int) <= a.spec_index((i + 1) as int));
        
        // Prove transitivity extension for the next iteration
        let i_int = i as int;
        let next_i_int = (i + 1) as int;
        
        assert(forall|p: int| 0 <= p <= next_i_int ==> 
               forall|q: int| p < q <= next_i_int ==> a.spec_index(p) <= a.spec_index(q)) by {
            forall|p: int, q: int| 0 <= p < q <= next_i_int implies a.spec_index(p) <= a.spec_index(q) by {
                if q <= i_int {
                    // Both p and q are in the previously verified range
                    assert(a.spec_index(p) <= a.spec_index(q));
                } else if p <= i_int && q == next_i_int {
                    // p is in previous range, q is the new element
                    if p == i_int {
                        assert(a.spec_index(p) <= a.spec_index(q));
                    } else {
                        assert(a.spec_index(p) <= a.spec_index(i_int));
                        assert(a.spec_index(i_int) <= a.spec_index(next_i_int));
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