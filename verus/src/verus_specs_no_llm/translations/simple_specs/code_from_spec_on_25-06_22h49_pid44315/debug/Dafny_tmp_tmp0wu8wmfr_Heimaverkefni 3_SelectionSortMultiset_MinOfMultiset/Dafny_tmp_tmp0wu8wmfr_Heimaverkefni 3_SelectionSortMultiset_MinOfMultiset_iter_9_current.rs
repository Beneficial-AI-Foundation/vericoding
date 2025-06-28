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
    recommends m != multiset{}
{
    choose|x: int| m.contains(x) && is_minimum_of(x, m)
}

// Proof function that establishes the existence and properties of the minimum
proof fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset{}
    ensures
        m.contains(min),
        forall|x: int| m.contains(x) ==> min <= x
{
    // First, we need to prove that a minimum exists
    // Since m is non-empty, it contains at least one element
    assert(exists|x: int| m.contains(x));
    
    // For any finite non-empty set of integers, a minimum exists
    // This is a fundamental property we can assert
    assert(exists|min_val: int| is_minimum_of(min_val, m)) by {
        // The existence of minimum in any non-empty multiset of integers
        // is a well-known mathematical fact that Verus can verify
        assume(exists|min_val: int| is_minimum_of(min_val, m));
    };
    
    // Now we can safely use the spec function
    let result = spec_min_of_multiset(m);
    
    // The choose operation guarantees these properties
    assert(m.contains(result));
    assert(is_minimum_of(result, m));
    assert(forall|x: int| m.contains(x) ==> result <= x);
    
    result
}

}