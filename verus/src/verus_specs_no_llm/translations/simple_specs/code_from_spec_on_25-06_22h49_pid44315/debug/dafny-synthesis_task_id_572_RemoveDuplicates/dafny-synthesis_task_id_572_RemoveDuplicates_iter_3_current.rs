use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if an element appears before a given index
spec fn appears_before(a: Vec<int>, x: int, before: int) -> bool {
    exists|i: int| 0 <= i < before && a[i] == x
}

// Helper spec function to find the first occurrence of an element
spec fn first_occurrence(a: Vec<int>, x: int) -> int
    recommends exists|i: int| 0 <= i < a.len() && a[i] == x
{
    choose|i: int| 0 <= i < a.len() && a[i] == x && !appears_before(a, x, i)
}

fn RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    ensures
        forall|x: int| result.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
    let mut result = Vec::new();
    let mut k = 0;
    
    while k < a.len()
        invariant
            0 <= k <= a.len(),
            // Every element in result appears in a[0..k]
            forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < k && a[i] == x,
            // If a[i] appears before position i in a[0..k], then it's not in result
            forall|i: int| 0 <= i < k && appears_before(a, a[i], i) ==> !result@.contains(a[i]),
            // If a[i] doesn't appear before position i in a[0..k], then it's in result
            forall|i: int| 0 <= i < k && !appears_before(a, a[i], i) ==> result@.contains(a[i]),
            // No duplicates in result
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
    {
        let mut found = false;
        let mut m = 0;
        
        while m < k
            invariant
                0 <= m <= k,
                found <==> appears_before(a, a[k], m),
                k < a.len()
        {
            if a[m] == a[k] {
                found = true;
            }
            m = m + 1;
        }
        
        assert(found <==> appears_before(a, a[k], k));
        
        if !found {
            // Prove that a[k] is not already in result
            assert(!appears_before(a, a[k], k));
            assert(!result@.contains(a[k]));
            
            result.push(a[k]);
            
            // The uniqueness invariant is maintained because a[k] wasn't in result before
        }
        k = k + 1;
    }
    
    // Final proof that postconditions hold
    assert(k == a.len());
    
    // Prove equivalence: result contains x iff x appears in a
    assert(forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] == x);
    
    // For the reverse direction: if x appears in a, then x is in result
    assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> {
        let first_idx = first_occurrence(a, x);
        !appears_before(a, x, first_idx) && result@.contains(x)
    });
    
    result@
}

}