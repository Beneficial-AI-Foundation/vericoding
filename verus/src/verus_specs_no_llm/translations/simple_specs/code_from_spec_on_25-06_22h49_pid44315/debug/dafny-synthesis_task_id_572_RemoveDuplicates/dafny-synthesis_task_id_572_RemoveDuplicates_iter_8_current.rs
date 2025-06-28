use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if an element appears before a given index
spec fn appears_before(a: Vec<int>, x: int, before: int) -> bool {
    exists|i: int| 0 <= i < before && i < a.len() && a[i] == x
}

// Helper spec function to find the first occurrence index
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
                if exists|i: int| 0 <= i < result@.len() - 1 && result@[i] == a[k] {
                    let bad_i = choose|i: int| 0 <= i < result@.len() - 1 && result@[i] == a[k];
                    // result@[bad_i] is in result, so by invariant it appears in a[0..k] as first occurrence
                    assert(exists|j: int| 0 <= j < k && a[j] == result@[bad_i] && !appears_before(a, result@[bad_i], j));
                    // But result@[bad_i] == a[k], so a[k] appears in a[0..k), contradicting !found
                    assert(appears_before(a, a[k], k));
                    assert(false);
                }
            };
        }
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == a.len());
    
    // Prove the biconditional postcondition
    assert(forall|x: int| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x) by {
        // Forward direction: if x is in result, then x is in a
        assert(forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] == x) by {
            // From loop invariant with k == a.len()
        };
        
        // Backward direction: if x is in a, then x is in result
        assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> result@.contains(x)) by {
            // For any x that exists in a, there must be a first occurrence
            // By the well-ordering principle and our loop invariant
            assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> {
                // There exists some first occurrence of x in a
                exists|first: int| 0 <= first < a.len() && a[first] == x && !appears_before(a, x, first)
            });
            
            // And by our loop invariant, when we process this first occurrence, we add it to result
            assert(forall|first: int| 0 <= first < a.len() && !appears_before(a, a[first], first) ==> result@.contains(a[first]));
        };
    };
    
    result@
}

}