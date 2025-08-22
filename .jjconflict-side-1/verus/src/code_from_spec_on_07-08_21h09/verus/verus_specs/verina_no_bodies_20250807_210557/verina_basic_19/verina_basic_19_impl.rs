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
        return true;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < a.len() - 1
        invariant 
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= a@[j + 1],
        decreases a.len() - i,
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

}

fn main() {}