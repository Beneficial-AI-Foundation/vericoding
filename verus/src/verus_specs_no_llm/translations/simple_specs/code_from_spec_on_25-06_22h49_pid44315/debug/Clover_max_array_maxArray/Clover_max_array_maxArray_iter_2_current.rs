use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxArray(a: Vec<int>) -> (m: int)
    requires
        a.len() >= 1
    ensures
        forall k :: 0 <= k < a.len() ==> m >= a.spec_index(k),
        exists k :: 0 <= k < a.len() && m == a.spec_index(k)
{
    let mut max = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall k :: 0 <= k < i ==> max >= a.spec_index(k),
            exists k :: 0 <= k < i && max == a.spec_index(k)
    {
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }
    
    // Proof that the postcondition holds
    assert(i == a.len());
    assert(forall k :: 0 <= k < a.len() ==> max >= a.spec_index(k));
    assert(exists k :: 0 <= k < a.len() && max == a.spec_index(k));
    
    max
}

}