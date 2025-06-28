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
    {
        if a[i] < a[minIdx] {
            minIdx = i;
            // Prove that minIdx is still in bounds after assignment
            assert(i < a.len());
            assert(lo <= i < a.len());
        }
        i = i + 1;
    }
    
    // After the loop, i == a.len(), so we need to prove the postcondition
    assert(i == a.len());
    assert(forall|x: nat| lo <= x < a.len() ==> a.spec_index(minIdx as nat) <= a.spec_index(x)) by {
        // The loop invariant gives us the property for x < i
        // Since i == a.len(), this covers all valid indices
        assert(forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x));
    };
    
    minIdx as nat
}

}