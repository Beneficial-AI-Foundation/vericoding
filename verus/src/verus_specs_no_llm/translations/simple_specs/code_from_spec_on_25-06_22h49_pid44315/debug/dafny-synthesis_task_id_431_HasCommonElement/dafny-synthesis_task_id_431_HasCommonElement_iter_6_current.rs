use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasCommonElement(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a.spec_index(i) == b.spec_index(j),
        !result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a.spec_index(i) != b.spec_index(j)
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a.spec_index(ii) != b.spec_index(jj)
    {
        let mut j = 0;
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                forall |ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a.spec_index(ii) != b.spec_index(jj),
                forall |jj: int| 0 <= jj < j ==> a.spec_index(i as int) != b.spec_index(jj)
        {
            if a.spec_index(i as int) == b.spec_index(j as int) {
                return true;
            }
            j += 1;
        }
        
        // After inner loop completes, we need to establish that a[i] != b[jj] for all jj
        // This is needed to maintain the outer loop invariant when i is incremented
        assert(forall |jj: int| 0 <= jj < b.len() ==> a.spec_index(i as int) != b.spec_index(jj));
        
        i += 1;
    }
    
    // At this point, we've checked all pairs and found no common elements
    // The outer loop invariant gives us what we need for the postcondition
    assert(forall |ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() ==> a.spec_index(ii) != b.spec_index(jj));
    false
}

}