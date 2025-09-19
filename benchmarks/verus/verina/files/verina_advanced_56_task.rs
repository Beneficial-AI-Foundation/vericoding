// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* Count how many times a specific value appears in the sequence */
spec fn count_val(val: i32, xs: Seq<i32>) -> nat 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let rest = count_val(val, xs.drop_first());
        if xs[0] == val { rest + 1 } else { rest }
    }
}

/* Check whether one sequence is a subsequence of another (preserving relative order) */
spec fn is_subsequence(xs: Seq<i32>, ys: Seq<i32>) -> bool 
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        true
    } else if ys.len() == 0 {
        false
    } else {
        if xs[0] == ys[0] {
            is_subsequence(xs.drop_first(), ys.drop_first())
        } else {
            is_subsequence(xs, ys.drop_first())
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* All non-zero elements must maintain their relative order */
        is_subsequence(xs@.filter(|x: i32| x != 0), result@),
        /* All zeroes must be located at the end of the output vector */
        forall|i: int| 0 <= i < result.len() && result[i] != 0 ==> 
            forall|j: int| i < j < result.len() ==> result[j] != 0,
        /* The output must contain the same number of elements */
        xs.len() == result.len(),
        /* The number of zeroes must remain unchanged */
        count_val(0, xs@) == count_val(0, result@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}