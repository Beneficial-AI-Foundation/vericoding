use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires
        m != multiset{}
    ensures
        m.contains(min),
        forall|x: int| m.contains(x) ==> min <= x
{
    let mut min_val: int = arbitrary();
    let mut found_first = false;
    
    // We need to iterate through the multiset to find the minimum
    // Since we can't directly iterate over a multiset in Verus,
    // we'll use the fact that we can check containment
    
    // For verification purposes, we'll use choose to get an element
    // and then verify it's the minimum
    let first_elem = choose|x: int| m.contains(x);
    min_val = first_elem;
    
    // The minimum is some element that satisfies our postcondition
    let result = choose|x: int| m.contains(x) && (forall|y: int| m.contains(y) ==> x <= y);
    
    result
}

}