// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed for the helper function. */
proof fn lemma_div_by_step(start: int, stop: int, step: int)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        (if step < 0 {
            (start - stop) / (-step)
        } else {
            (stop - start) / step
        }) >= 0,
{
    if step < 0 {
        assert(start > stop);
    } else {
        assert(start < stop);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn arange_length(start: int, stop: int, step: int) -> nat
{
    if step != 0 {
        if step < 0 {
            if start > stop {
                ((start - stop) / (-step)) as nat
            } else {
                0
            }
        } else {
            if start < stop {
                ((stop - start) / step) as nat
            } else {
                0
            }
        }
    } else {
        0
    }
}

fn arange(start: i8, stop: i8, step: i8) -> (result: Vec<i8>)
    requires 
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        result@.len() == arange_length(start as int, stop as int, step as int),
        result@.len() > 0,
        result@[0] == start as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The type mismatch error has been resolved by ensuring that `i` is explicitly cast to `int` when used in arithmetic operations within the `forall` quantifier. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut current = start;
    proof {
        lemma_div_by_step(start as int, stop as int, step as int);
        assert((step as int) != 0);
        if (step as int) < 0 {
            assert((start as int) > (stop as int));
        } else {
            assert((start as int) < (stop as int));
        }
    }

    while (step < 0 && current > stop) || (step > 0 && current < stop)
        invariant
            (result.len() as int) <= arange_length(start as int, stop as int, step as int),
            current as int == start as int + (result.len() as int) * (step as int),
            forall|i: nat| #![auto]
                0 <= i && (i as int) < result.len()
                    ==> result@[i as int] == (start as int + (i as int) * (step as int)) as i8,
            result.len() == 0 || result@[0] == start as int
        decreases if step < 0 { current as int - stop as int } else { stop as int - current as int }
    {
        result.push(current);
        current = current + step;
    }

    result
}
// </vc-code>


}
fn main() {}