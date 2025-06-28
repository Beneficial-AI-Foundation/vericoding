use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len())) || (exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            a.spec_index(..i) == b.spec_index(..i),
    {
        if a[i] < b[i] {
            assert(a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) < b.spec_index(i));
            return true;
        } else if a[i] > b[i] {
            assert(a.spec_index(..i) == b.spec_index(..i) && a.spec_index(i) > b.spec_index(i));
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    // Return true if a is not longer than b (a is prefix of b or equal)
    let result = a.len() <= b.len();
    
    if result {
        assert(a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len()));
    } else {
        // a.len() > b.len(), so b is a proper prefix of a
        assert(b.len() < a.len());
        assert(a.spec_index(..b.len()) == b.spec_index(..));
        // This means a is lexicographically greater than b
    }
    
    result
}

}