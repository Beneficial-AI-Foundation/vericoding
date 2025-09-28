// <vc-preamble>
use vstd::prelude::*;

verus! {

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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed. The previous helper was unnecessary and caused compilation errors. */
// </vc-helpers>

// <vc-spec>
fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    ensures

        is_subsequence(xs@.filter(|x: i32| x != 0), result@),

        forall|i: int| 0 <= i < result.len() && result[i] != 0 ==> 
            forall|j: int| i < j < result.len() ==> result[j] != 0,

        xs.len() == result.len(),

        count_val(0, xs@) == count_val(0, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting issues for `nat` and `int` by ensuring `nat` operations result in `nat` directly and using `as int` only when necessary like with comparisons and sums with existing `int` values. */
{
    let mut new_vec: Vec<i32> = Vec::new();
    let mut num_zeros: nat = 0; // Initialize num_zeros as nat

    let mut i: usize = 0;

    while i < xs.len()
        invariant
            0 <= i as int <= xs.len() as int,
            new_vec.len() as nat + num_zeros == i as nat,
            forall |j: int| 0 <= j < new_vec.len() ==> new_vec[j] != 0,
            num_zeros == count_val(0, xs@.subrange(0, i as int)), 
            is_subsequence(xs@.subrange(0, i as int).filter(|x: i32| x != 0), new_vec@),
            new_vec.len() <= xs.len()
        decreases xs.len() - i
    {
        if xs[i] != 0 {
            new_vec.push(xs[i]);
        } else {
            num_zeros = num_zeros + 1;
        }
        i = i + 1;
    }

    let total_non_zeros = new_vec.len();
    let total_zeros = num_zeros;

    while num_zeros > 0
        invariant
            0 < num_zeros as int <= total_zeros as int,
            new_vec.len() as nat == total_non_zeros as nat + (total_zeros - num_zeros),
            new_vec.len() <= xs.len(),
            forall |j: int| 0 <= j < total_non_zeros ==> new_vec[j] != 0,
            forall |j: int| total_non_zeros <= j < new_vec.len() ==> new_vec[j] == 0
        decreases num_zeros
    {
        new_vec.push(0);
        num_zeros = num_zeros - 1;
    }

    new_vec
}
// </vc-code>

}
fn main() {}