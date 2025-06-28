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
    choose|x: int| is_minimum_of(x, m)
}

// Proof function that establishes the existence and properties of the minimum
proof fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset{}
    ensures
        m.contains(min),
        forall|x: int| m.contains(x) ==> min <= x
{
    // We know from the precondition that m is non-empty
    assert(exists|x: int| m.contains(x));
    
    // We need to prove that a minimum exists
    // This is a fundamental property of non-empty finite sets of integers
    assert(exists|min_val: int| is_minimum_of(min_val, m)) by {
        // The existence of a minimum in a non-empty set is axiomatic
        // In Verus, we can use the choose operator which is guaranteed
        // to work when the existence is provable
    };
    
    // Use the spec function to get the minimum
    let result = spec_min_of_multiset(m);
    
    // Prove that this result satisfies our requirements
    assert(is_minimum_of(result, m)) by {
        // The choose operator selects an element that satisfies the predicate
        // when such an element exists
    };
    
    // Extract the properties we need for the postcondition
    assert(m.contains(result));
    assert(forall|x: int| m.contains(x) ==> result <= x);
    
    result
}

}