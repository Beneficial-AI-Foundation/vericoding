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
/* code modified by LLM (iteration 5): Fixed integer literal types */
{
    let mut result: Vec<i32> = Vec::new();
    let mut zero_count: int = 0.to_int();

    for i in 0..xs.len() {
        if xs[i] == 0 {
            zero_count = zero_count + 1.to_int();
        } else {
            result.push(xs[i]);
        }
    }

    let mut i: int = 0.to_int();
    while i < zero_count
        invariant
            result.len() == (xs.len() as int - zero_count) + i,
            0.to_int() <= i,
            i <= zero_count,
        decreases zero_count - i
    {
        result.push(0);
        i = i + 1.to_int();
    }
    
    result
}
// </vc-code>

}
fn main() {}