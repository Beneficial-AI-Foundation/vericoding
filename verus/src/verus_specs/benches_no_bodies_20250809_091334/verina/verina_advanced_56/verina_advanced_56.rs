use vstd::prelude::*;

verus! {

// Count how many times a specific value appears in the list
spec fn count_val(val: i32, xs: Seq<i32>) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0nat
    } else {
        let rest = count_val(val, xs.drop_first());
        if xs.first() == val {
            rest + 1
        } else {
            rest
        }
    }
}

// Check whether one list is a subsequence of another (preserving relative order)
spec fn is_subsequence(xs: Seq<i32>, ys: Seq<i32>) -> bool
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        true
    } else if ys.len() == 0 {
        false
    } else {
        let x = xs.first();
        let y = ys.first();
        if x == y {
            is_subsequence(xs.drop_first(), ys.drop_first())
        } else {
            is_subsequence(xs, ys.drop_first())
        }
    }
}

// Helper function to filter out zeros
spec fn filter_nonzeros(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else {
        let first = xs.first();
        let rest = filter_nonzeros(xs.drop_first());
        if first != 0 {
            seq![first] + rest
        } else {
            rest
        }
    }
}

// Helper function to filter zeros
spec fn filter_zeros(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else {
        let first = xs.first();
        let rest = filter_zeros(xs.drop_first());
        if first == 0 {
            seq![first] + rest
        } else {
            rest
        }
    }
}

// Check if all elements in a sequence are zeros
spec fn all_zeros(xs: Seq<i32>) -> bool
    decreases xs.len()
{
    if xs.len() == 0 {
        true
    } else {
        xs.first() == 0 && all_zeros(xs.drop_first())
    }
}

// Drop elements while they satisfy a predicate
spec fn drop_while_nonzero(xs: Seq<i32>) -> Seq<i32>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else if xs.first() != 0 {
        drop_while_nonzero(xs.drop_first())
    } else {
        xs
    }
}

spec fn move_zeroes_precond(xs: Seq<i32>) -> bool {
    true
}

spec fn move_zeroes_postcond(xs: Seq<i32>, result: Seq<i32>) -> bool {
    // 1. All non-zero elements must maintain their relative order
    is_subsequence(filter_nonzeros(xs), result) &&
    
    // 2. All zeroes must be located at the end of the output list
    all_zeros(drop_while_nonzero(result)) &&
    
    // 3. The output must contain the same number of elements,
    //    and the number of zeroes must remain unchanged
    count_val(0, xs) == count_val(0, result) &&
    xs.len() == result.len()
}

fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    requires move_zeroes_precond(xs@)
    ensures move_zeroes_postcond(xs@, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

} // verus!