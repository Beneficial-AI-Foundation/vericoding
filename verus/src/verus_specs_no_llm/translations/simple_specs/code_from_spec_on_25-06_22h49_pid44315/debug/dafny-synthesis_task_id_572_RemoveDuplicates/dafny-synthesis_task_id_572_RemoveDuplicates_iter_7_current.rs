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
        forall|x: int| result.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
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
            }
            m = m + 1;
        }
        
        assert(found <==> appears_before(a, a[k], k));
        
        if !found {
            result.push(a[k]);
            
            // Prove that adding a[k] maintains no duplicates
            assert(forall|i: int| 0 <= i < result@.len() - 1 ==> result@[i] != a[k]) by {
                assert(forall|i: int| 0 <= i < result@.len() - 1 ==> {
                    let x = result@[i];
                    // x is in result, so it appears in a[0..k] and is first occurrence
                    exists|j: int| 0 <= j < k && a[j] == x && !appears_before(a, x, j)
                });
                // Since !appears_before(a, a[k], k), we know a[k] doesn't appear in a[0..k)
                // So a[k] can't equal any element already in result
            };
        }
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == a.len());
    
    // Prove both directions of the biconditional
    assert(forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] == x) by {
        // From loop invariant: every element in result appears in a[0..k] where k == a.len()
        assert(forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < k && a[i] == x);
    };
    
    assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> result@.contains(x)) by {
        // For any x that exists in a, consider its first occurrence
        assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> {
            // There must be some first occurrence
            let first_idx = choose|i: int| 0 <= i < a.len() && a[i] == x && !appears_before(a, x, i);
            // By loop invariant, this first occurrence gets added to result
            result@.contains(x)
        });
    };
    
    result@
}

}