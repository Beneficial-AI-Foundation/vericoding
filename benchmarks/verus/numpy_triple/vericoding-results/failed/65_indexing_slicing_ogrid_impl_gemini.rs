// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Added a lemma to state implicit preconditions of ogrid] */
proof fn lemma_ogrid_value_in_bounds(start: i8, stop: i8, step: i8, n: usize, i: int)
    requires
        0 <= i < n,
        step != 0,
    ensures
        {
            let val = (start as int) + i * (step as int);
            i8::MIN <= val && val <= i8::MAX
        },
        if step > 0 {
            (start as int) + i * (step as int) < (stop as int)
        } else {
            (stop as int) < (start as int) + i * (step as int)
        },
{
}

// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Used int for calculations and a lemma to prove bounds] */
    let mut result: Vec<i8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (start as int) + j * (step as int),
            forall|j: int| 0 <= j < i ==> 
                if step > 0 {
                    (start as int) <= result@[j] && result@[j] < (stop as int)
                } else {
                    (stop as int) < result@[j] && result@[j] <= (start as int)
                },
        decreases n - i
    {
        lemma_ogrid_value_in_bounds(start, stop, step, n, i as int);

        let val_int = (start as int) + (i as int) * (step as int);
        let val = val_int as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}