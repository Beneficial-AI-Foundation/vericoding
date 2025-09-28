// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed for this proof */
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid int usage in exec choose; use input[i] and maintain invariant */
    let n = input.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
            forall|j: int| 0 <= j && j < i as int ==> res@[j] == func(input@[j]),
        decreases n - i
    {
        let x: i8 = choose|x: i8| x == func(input[i]);
        res.push(x);
        proof {
            assert(0 <= i as int && i as int < input.len() as int);
            assert(input@[i as int] == input[i]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}