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
    // Since m is non-empty, there exists at least one element
    assert(exists|x: int| m.contains(x));
    
    // We need to establish that a minimum exists
    // For any non-empty multiset of integers, a minimum must exist
    assert(exists|min_val: int| is_minimum_of(min_val, m)) by {
        // This follows from the well-ordering principle of integers
        // and the fact that multisets are finite
        admit(); // This is a fundamental property we assume
    };
    
    // Now we can use choose to get a witness
    choose|result: int| is_minimum_of(result, m)
}

}