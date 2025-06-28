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

fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset{}
    ensures
        m.contains(min),
        forall|x: int| m.contains(x) ==> min <= x
{
    // Since we can't directly compute from multisets in exec code,
    // we need to use proof_from_false to indicate this is a specification-only function
    // In practice, this would be implemented by converting the multiset
    // to a concrete data structure first.
    
    proof {
        // We know from the precondition that m is non-empty
        assert(exists|x: int| m.contains(x));
        // We can prove that a minimum exists
        assert(exists|min_val: int| is_minimum_of(min_val, m));
    }
    
    // Use the spec function to get the minimum
    let result = spec_min_of_multiset(m);
    
    proof {
        // Prove that our result satisfies the postcondition
        assert(is_minimum_of(result, m));
        assert(m.contains(result));
        assert(forall|x: int| m.contains(x) ==> result <= x);
    }
    
    result
}

}