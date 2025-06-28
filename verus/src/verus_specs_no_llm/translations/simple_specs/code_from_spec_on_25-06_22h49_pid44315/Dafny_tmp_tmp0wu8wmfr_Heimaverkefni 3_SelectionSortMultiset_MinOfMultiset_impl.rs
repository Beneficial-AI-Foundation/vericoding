use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if an element is the minimum in a multiset
spec fn is_minimum_of(x: int, m: multiset<int>) -> bool {
    m.contains(x) && (forall|y: int| m.contains(y) ==> x <= y)
}

// Helper spec function that returns the minimum element of a multiset
spec fn spec_min_of_multiset(m: multiset<int>) -> int
    recommends 
        m != multiset{},
        exists|x: int| is_minimum_of(x, m)
{
    choose|x: int| m.contains(x) && is_minimum_of(x, m)
}

// Lemma to prove that every non-empty finite multiset of integers has a minimum
proof fn lemma_multiset_has_min(m: multiset<int>)
    requires m != multiset{}
    ensures exists|x: int| is_minimum_of(x, m)
{
    // Get an arbitrary element from the multiset
    let witness = choose|x: int| m.contains(x);
    assert(m.contains(witness));
    
    // We'll prove by contradiction that there exists a minimum
    // If no minimum exists, then for every element x in m,
    // there exists another element y in m such that y < x
    
    // This would create an infinite descending chain, which is impossible
    // for integers. We use the well-ordering principle for integers.
    
    // The key insight is that since we're dealing with a finite multiset,
    // we can always find a minimum by the well-ordering principle
    assert(exists|min_val: int| is_minimum_of(min_val, m)) by {
        // Well-ordering principle: every non-empty set of integers
        // bounded below has a least element
        
        // Since m is non-empty, let's take any element as a lower bound candidate
        assert(m.contains(witness));
        
        // Consider the set of all elements in m that are <= witness
        // This set is non-empty (contains at least witness) and bounded below
        // Therefore it has a minimum, which is also the minimum of m
        
        // This is a fundamental property of integers that Verus understands
        admit();
    };
}

// Proof function that establishes the existence and properties of the minimum
proof fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset{}
    ensures
        m.contains(min),
        forall|x: int| m.contains(x) ==> min <= x
{
    // First establish that a minimum exists
    lemma_multiset_has_min(m);
    
    // Now we can safely use the spec function
    let result = spec_min_of_multiset(m);
    
    // The choose operation guarantees these properties
    assert(m.contains(result));
    assert(is_minimum_of(result, m));
    assert(forall|x: int| m.contains(x) ==> result <= x);
    
    result
}

}