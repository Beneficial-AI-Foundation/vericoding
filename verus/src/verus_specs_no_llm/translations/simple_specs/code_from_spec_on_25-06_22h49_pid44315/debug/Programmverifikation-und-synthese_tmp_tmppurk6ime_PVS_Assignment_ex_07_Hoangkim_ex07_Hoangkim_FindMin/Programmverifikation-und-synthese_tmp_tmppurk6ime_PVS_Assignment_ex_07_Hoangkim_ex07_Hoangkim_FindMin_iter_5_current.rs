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
            minIdx < a.len(),
            forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x)
    {
        if a[i] < a[minIdx] {
            minIdx = i;
        }
        i = i + 1;
    }
    
    proof {
        // After the loop, i == a.len()
        assert(i == a.len());
        // The loop invariant gives us the property for all x in [lo, i)
        assert(forall|x: nat| lo <= x < i ==> a.spec_index(minIdx as nat) <= a.spec_index(x));
        // Since i == a.len(), this extends to the full range
        assert(forall|x: nat| lo <= x < a.len() ==> a.spec_index(minIdx as nat) <= a.spec_index(x));
    }
    
    minIdx as nat
}

}