use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minArray(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        forall|k| 0 <= k < a.len() ==> m <= a.spec_index(k),
        exists|k| 0 <= k < a.len() && m == a.spec_index(k)
{
    let mut min = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k| 0 <= k < i ==> min <= a.spec_index(k),
            exists|k| 0 <= k < i && min == a.spec_index(k)
    {
        if a[i] < min {
            min = a[i];
        }
        i = i + 1;
        
        // Proof annotation to help with the invariant
        proof {
            assert(forall|k| 0 <= k < i ==> min <= a.spec_index(k));
            assert(exists|k| 0 <= k < i && min == a.spec_index(k));
        }
    }
    
    // Final proof that the postcondition holds
    proof {
        assert(i == a.len());
        assert(forall|k| 0 <= k < a.len() ==> min <= a.spec_index(k));
        assert(exists|k| 0 <= k < a.len() && min == a.spec_index(k));
    }
    
    min
}

}