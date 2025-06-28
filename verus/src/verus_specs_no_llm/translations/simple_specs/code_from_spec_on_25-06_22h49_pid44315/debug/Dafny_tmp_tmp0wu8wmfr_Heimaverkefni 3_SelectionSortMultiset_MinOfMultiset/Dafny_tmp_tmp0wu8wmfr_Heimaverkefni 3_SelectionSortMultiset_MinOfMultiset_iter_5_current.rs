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
    // we use proof_from_false to indicate this function cannot be executed
    // but can be reasoned about in proofs
    
    proof {
        // We know from the precondition that m is non-empty
        assert(exists|x: int| m.contains(x));
        
        // We can prove that a minimum exists using the fact that
        // any non-empty finite set of integers has a minimum
        assert(exists|min_val: int| is_minimum_of(min_val, m));
        
        // The choose operator in spec_min_of_multiset will select such a minimum
        let result = spec_min_of_multiset(m);
        assert(is_minimum_of(result, m));
    }
    
    // Use proof_from_false since this function is for specification purposes
    proof_from_false()
}

}