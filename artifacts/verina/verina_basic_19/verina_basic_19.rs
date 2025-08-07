use vstd::prelude::*;

verus! {

// Precondition for isSorted - always true in this case  
spec fn is_sorted_precond(a: Seq<i32>) -> bool {
    true
}

// Postcondition specification
spec fn is_sorted_postcond(a: Seq<i32>, result: bool) -> bool {
    (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]) <==> result
}

// Check if array is sorted
fn is_sorted(a: &[i32]) -> (result: bool)
    requires is_sorted_precond(a@),
    ensures is_sorted_postcond(a@, result),
{
    if a.len() <= 1 {
        // Arrays of length 0 or 1 are trivially sorted
        true
    } else {
        // Check all consecutive pairs
        let mut i = 0;
        
        while i < a.len() - 1
            invariant 
                0 <= i <= a.len() - 1,
                forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= a@[j + 1],
            decreases a.len() - 1 - i,
        {
            if a[i] > a[i + 1] {
                // Found a pair that's not sorted
                assert(a@[i as int] > a@[i as int + 1]);
                assert(!(forall|j: int| 0 <= j < a@.len() - 1 ==> #[trigger] a@[j] <= a@[j + 1]));
                return false;
            }
            i += 1;
        }
        
        // All pairs checked and sorted
        assert(forall|j: int| 0 <= j < a@.len() - 1 ==> #[trigger] a@[j] <= a@[j + 1]);
        true
    }
}

}

fn main() {}