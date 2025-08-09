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
    
    for i in 0..a.len() - 1
        invariant
            /* code modified by LLM (iteration 1): added trigger annotations to the quantifier */
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= #[trigger] a@[j + 1]
    {
        if a[i] > a[i + 1] {
            return false;
        }
    }
    
    true
}

}

fn main() {}