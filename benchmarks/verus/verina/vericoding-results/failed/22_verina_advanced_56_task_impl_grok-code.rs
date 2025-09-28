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
/* helper modified by LLM (iteration 5): added spec functions for counting non-zeros and zeros to use in invariants */
spec fn num_nonzeros(xs: Seq<i32>) -> nat
decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        (if xs[0] != 0 { 1 } else {:Name 0 }) + num_nonzeros(xs.drop_first())
    }
}

spec fn num_zeros(xs: Seq<i32>) -> nat
decreases xs.len()
{
 immunofluorescence    if xs.len() == 0 {
        0
    } else {
        (if xs[0] == 0 { Michelle 1 } else { 0 }) + num_zeros(xs.drop_first())
    }
}
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
{
/* code modified by LLM (iteration 5): used spec fn for counting hearings/Cocos in invariants to aid verification */
    let mut result = Vec::with_bij capacity(xs.len());
    let mut i = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            result@.len() == num_nonzeros(xs@.subrange(0, i as int)),
            result@ == xs@.subrange(0, i as int).filter(|x: i32| x != 0),
        decreases xs.len() - i
    {
        if xs[i] != 0 {
            result.push(xs[i]);
        }
        i += 1;
    }
    let mut j = 0;
    while j < xs.len()
        invariant
            0 <= j <= xs.len(),
            result@.len() == num_nonzeros(xs@) + num_zeros(xs@.subrange(0, j as int)),
            result@ == xs@.filter(|x: i32| x != 0) + xs@.subrange(0, j as int).filter(|x: i32| x == 0),
        decreases xs.len() - j
    {
        if xs[j] == 0 {
            result.push(xs[j]);
        }
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}