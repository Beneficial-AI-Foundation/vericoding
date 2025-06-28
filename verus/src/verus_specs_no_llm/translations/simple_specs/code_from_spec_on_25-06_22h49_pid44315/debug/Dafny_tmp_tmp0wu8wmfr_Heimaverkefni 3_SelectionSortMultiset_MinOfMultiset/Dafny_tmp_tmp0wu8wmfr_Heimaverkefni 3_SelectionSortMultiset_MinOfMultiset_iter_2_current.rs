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
    // Since we can't iterate over multisets directly in exec code,
    // we use the spec function and prove it satisfies our requirements
    let result = spec_min_of_multiset(m);
    
    // Prove that our result satisfies the postconditions
    assert(m.contains(result));
    assert(forall|x: int| m.contains(x) ==> result <= x);
    
    result
}

}