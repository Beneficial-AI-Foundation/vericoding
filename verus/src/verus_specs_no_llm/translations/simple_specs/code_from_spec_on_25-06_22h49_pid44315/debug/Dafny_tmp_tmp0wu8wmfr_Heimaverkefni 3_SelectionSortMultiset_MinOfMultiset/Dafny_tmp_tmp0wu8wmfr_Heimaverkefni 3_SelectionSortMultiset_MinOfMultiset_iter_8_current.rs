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
    // We use the spec function to get the minimum
    let result = spec_min_of_multiset(m);
    
    // The spec function guarantees the properties we need
    assert(is_minimum_of(result, m));
    assert(m.contains(result));
    assert(forall|x: int| m.contains(x) ==> result <= x);
    
    result
}

}