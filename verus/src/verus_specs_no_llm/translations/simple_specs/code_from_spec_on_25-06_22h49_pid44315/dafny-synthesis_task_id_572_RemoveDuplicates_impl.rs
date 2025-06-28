use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if an element appears before a given index
spec fn appears_before(a: Vec<int>, x: int, before: int) -> bool {
    exists|i: int| 0 <= i < before && i < a.len() && a[i] == x
}

fn RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    ensures
        // Every element in result exists in the original array
        forall|x: int| result.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        // Every element that exists in the original array is in the result
        forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> result.contains(x),
        // No duplicates in result
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
    let mut result = Vec::new();
    let mut k = 0;
    
    while k < a.len()
        invariant
            0 <= k <= a.len(),
            // Every element in result appears in a[0..k] and is the first occurrence
            forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < k && a[i] == x && !appears_before(a, x, i),
            // If a[i] is the first occurrence in a[0..k], then it's in result
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
                assert(appears_before(a, a[k], m + 1));
            }
            m = m + 1;
        }
        
        assert(found <==> appears_before(a, a[k], k));
        
        if !found {
            result.push(a[k]);
            
            // Prove that adding a[k] maintains no duplicates
            assert(forall|i: int| 0 <= i < result@.len() - 1 ==> result@[i] != a[k]) by {
                // Proof by contradiction
                let old_len = result@.len() - 1;
                assert(forall|i: int| 0 <= i < old_len ==> {
                    let elem = result@[i];
                    if elem == a[k] {
                        // elem is in result, so by invariant it appears in a[0..k] as first occurrence
                        assert(exists|j: int| 0 <= j < k && a[j] == elem && !appears_before(a, elem, j));
                        // But elem == a[k], so a[k] appears in a[0..k), contradicting !found
                        assert(appears_before(a, a[k], k));
                        assert(false);
                    }
                    elem != a[k]
                });
            };
        }
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == a.len());
    
    // The postconditions follow from the loop invariants
    result@
}

}