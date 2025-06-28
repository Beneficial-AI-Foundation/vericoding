use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to compare slices
spec fn slices_equal(a: Vec<int>, b: Vec<int>, end: int) -> bool {
    end >= 0 && end <= a.len() && end <= b.len() &&
    forall|j: int| 0 <= j < end ==> a[j] == b[j]
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a@ == b@.subrange(0, a.len() as int)) || (exists|k| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k])
{
    let mut i = 0;
    
    while i < a.len() && i < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            forall|j: int| 0 <= j < i ==> a[j] == b[j],
    {
        if a[i] < b[i] {
            // Found position where a[i] < b[i]
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int));
            return true;
        } else if a[i] > b[i] {
            // Found position where a[i] > b[i], so leq is false
            return false;
        }
        i += 1;
    }
    
    // If we reach here, all compared elements are equal
    // Return true if a is not longer than b
    if a.len() <= b.len() {
        // Prove that a@ == b@.subrange(0, a.len() as int)
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] == b[j]);
        assert(a@ == b@.subrange(0, a.len() as int)) by {
            assert(a@.len() == a.len());
            assert(b@.subrange(0, a.len() as int).len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@.subrange(0, a.len() as int)[j]) by {
                assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == a[j as usize]);
                assert(forall|j: int| 0 <= j < a.len() ==> b@.subrange(0, a.len() as int)[j] == b@[j]);
                assert(forall|j: int| 0 <= j < a.len() ==> a[j as usize] == b[j as usize]);
            }
        };
        true
    } else {
        // a.len() > b.len(), so first condition fails
        // Need to show second condition also fails
        assert(!(exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k])) by {
            assert(forall|j: int| 0 <= j < b.len() ==> a[j] == b[j]);
            if exists|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k] {
                let witness = choose|k: int| 0 <= k < a.len() && k < b.len() && a@.subrange(0, k) == b@.subrange(0, k) && a[k] < b[k];
                assert(a[witness] == b[witness]);  // from our invariant
                assert(a[witness] < b[witness]);   // from the existence condition
                assert(false);
            }
        };
        false
    }
}

}