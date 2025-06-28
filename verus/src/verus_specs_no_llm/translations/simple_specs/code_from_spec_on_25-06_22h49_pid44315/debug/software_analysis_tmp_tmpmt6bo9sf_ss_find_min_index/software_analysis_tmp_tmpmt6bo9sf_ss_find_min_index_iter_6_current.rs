use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find_min_index(a: Vec<int>, s: int, e: int) -> (min_i: int)
    requires
        a.len() > 0,
        0 <= s < a.len(),
        e <= a.len(),
        e > s
    ensures
        min_i >= s,
        min_i < e,
        forall k: int :: s <= k < e ==> a.spec_index(min_i) <= a.spec_index(k)
{
    let mut min_i = s;
    let mut i = s + 1;
    
    while i < e
        invariant
            s <= min_i < e,
            s < i <= e,
            min_i < a.len(),
            i <= a.len(),
            0 <= min_i < a.len(),
            forall k: int :: s <= k < i ==> a.spec_index(min_i) <= a.spec_index(k)
    {
        // Explicit bounds assertions for Verus verification
        assert(0 <= i < a.len());
        assert(0 <= min_i < a.len());
        
        if a.spec_index(i) < a.spec_index(min_i) {
            min_i = i;
        }
        i = i + 1;
    }
    
    // Final assertion to help with postcondition
    assert(forall k: int :: s <= k < i ==> a.spec_index(min_i) <= a.spec_index(k));
    assert(i == e);
    
    min_i
}

}