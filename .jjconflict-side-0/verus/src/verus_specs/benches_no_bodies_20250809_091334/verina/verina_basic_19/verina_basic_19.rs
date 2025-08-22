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
    return false;  // TODO: Remove this line and implement the function body
}

}

fn main() {}