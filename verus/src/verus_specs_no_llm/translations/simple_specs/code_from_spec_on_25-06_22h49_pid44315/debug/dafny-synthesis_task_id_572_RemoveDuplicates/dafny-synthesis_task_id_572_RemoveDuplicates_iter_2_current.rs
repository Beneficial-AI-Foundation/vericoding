use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
            forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < k && a[i] == x,
            forall|i: int| 0 <= i < k && (exists|j: int| 0 <= j < i && a[j] == a[i]) ==> !result@.contains(a[i]),
            forall|i: int| 0 <= i < k && (forall|j: int| 0 <= j < i ==> a[j] != a[i]) ==> result@.contains(a[i]),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
    {
        let mut found = false;
        let mut m = 0;
        
        while m < k
            invariant
                0 <= m <= k,
                found <==> exists|j: int| 0 <= j < m && a[j] == a[k],
                k < a.len()
        {
            if a[m] == a[k] {
                found = true;
                assert(exists|j: int| 0 <= j < m + 1 && a[j] == a[k]);
            }
            m = m + 1;
        }
        
        if !found {
            // Prove that a[k] is not already in result
            assert(forall|j: int| 0 <= j < k ==> a[j] != a[k]);
            assert(!result@.contains(a[k]));
            
            // Store old result for proof
            let old_result = result@;
            result.push(a[k]);
            
            // Prove uniqueness is maintained
            assert(forall|i: int, j: int| 0 <= i < j < old_result.len() ==> old_result[i] != old_result[j]);
            assert(forall|i: int| 0 <= i < old_result.len() ==> old_result[i] != a[k]);
            assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
        }
        k = k + 1;
    }
    
    // Final assertions to prove postconditions
    assert(k == a.len());
    
    // Prove first postcondition: result contains x iff x appears in a
    assert(forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < a.len() && a[i] == x);
    assert(forall|x: int| (exists|i: int| 0 <= i < a.len() && a[i] == x) ==> {
        let first_i = choose|i: int| 0 <= i < a.len() && a[i] == x && (forall|j: int| 0 <= j < i ==> a[j] != x);
        result@.contains(x)
    });
    
    // Prove second postcondition: no duplicates in result
    assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
    
    result@
}

}