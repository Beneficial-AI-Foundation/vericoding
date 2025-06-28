use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMin(a: Vec<int>, lo: nat) -> (minIdx: nat)
    requires
        a.len() > 0 && lo < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall|x: nat| lo <= x < a.len() ==> a.spec_index(minIdx) <= a.spec_index(x)
{
    let mut minIdx: usize = lo as usize;
    let mut i: usize = (lo + 1) as usize;
    
    while i < a.len()
        invariant
            a.len() > 0,
            lo < a.len(),
            lo <= minIdx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x),
            minIdx < a.len(),
            i <= usize::MAX,
            minIdx <= usize::MAX,
    {
        if a[i] < a[minIdx] {
            minIdx = i;
        }
        i = i + 1;
    }
    
    // Prove the postcondition holds
    assert(i == a.len());
    assert(forall|x: nat| lo <= x < a.len() ==> a.spec_index(minIdx as nat) <= a.spec_index(x)) by {
        // From the loop invariant, we know:
        // forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x)
        // Since i == a.len() after the loop, this means:
        // forall|x: nat| lo <= x < a.len() ==> a.spec_index(minIdx as nat) <= a.spec_index(x)
        assert(i == a.len());
        assert(forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x));
    };
    
    minIdx as nat
}

}