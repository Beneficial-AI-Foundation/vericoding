use vstd::prelude::*;

verus! {

// Precondition: the list is sorted (pairwise less than)
spec fn is_sorted(xs: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j]
}

spec fn search_insert_precond(xs: Seq<int>, target: int) -> bool {
    is_sorted(xs)
}

// Helper function to check if all elements before index are less than target
spec fn all_before_less(xs: Seq<int>, target: int, result: int) -> bool {
    forall|i: int| 0 <= i < result ==> xs[i] < target
}

// Postcondition specification
spec fn search_insert_postcond(xs: Seq<int>, target: int, result: int) -> bool {
    let in_bounds = result <= xs.len();
    let all_before_less = all_before_less(xs, target, result);
    let inserted_correctly = result < xs.len() ==> target <= xs[result];
    in_bounds && all_before_less && inserted_correctly
}

// Recursive helper function that mirrors the Lean implementation
fn helper(ys: &Vec<int>, target: int, idx: usize) -> (result: usize)
    requires
        idx <= ys.len(),
        is_sorted(ys@),
        forall|i: int| 0 <= i < idx ==> ys@[i] < target,
    ensures
        idx <= result <= ys.len(),
        forall|i: int| idx <= i < result ==> ys@[i] < target,
        result < ys.len() ==> target <= ys@[result as int],
    decreases 
        ys.len() - idx,
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Main searchInsert function following the Lean structure
fn search_insert(xs: &Vec<int>, target: int) -> (result: usize)
    requires 
        search_insert_precond(xs@, target),
    ensures 
        search_insert_postcond(xs@, target, result as int),
{
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {
    // TODO: Remove this comment and implement the function body
}