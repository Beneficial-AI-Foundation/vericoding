// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec accessor for vector elements */
spec fn get(a: &Vec<i32>, i: int) -> int
    requires 0 <= i, i < a.len() as int
{
    a[i as usize] as int
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use ghost accumulator via spec accessor */
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    let ghost mut gi: int = 0;
    let ghost mut gacc: int = 0;
    while i < a.len()
        invariant
            0 <= gi,
            gi <= a.len() as int,
            gi == i as int,
            gacc == sum_to(a, gi),
        decreases a.len() - i
    {
        let v: i32 = a[i];
        acc = acc + v;
        i = i + 1;
        ghost {
            gacc = gacc + get(a, gi);
            gi = gi + 1;
        }
    }
    ghost {
        assert(gacc == sum_to(a, a.len() as int));
    }
    let result: i32 = acc;
    result
}
// </vc-code>

}
fn main() {}