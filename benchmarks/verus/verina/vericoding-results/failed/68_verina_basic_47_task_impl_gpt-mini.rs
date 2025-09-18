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
/* helper modified by LLM (iteration 5): proof that sum_to(a, i+1) == sum_to(a, i) + a@[i] */
fn sum_to_step(a: &Vec<i32>, i: int)
    requires
        0 <= i && i < a.len() as int,
    ensures
        sum_to(a, i + 1) == sum_to(a, i) + a@[i],
    decreases
        a.len() as int - i
{
    proof {
        reveal(sum_to);
        assert(sum_to(a, i + 1) == sum_to(a, i) + a@[i]);
    }
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
    /* code modified by LLM (iteration 5): iterate using int index and sequence-indexing a@[i] to accumulate and establish spec */
    let mut i: int = 0;
    let mut s: i32 = 0;
    while i < a.len() as int
        invariant
            0 <= i,
            (s as int) == sum_to(a, i),
        decreases a.len() as int - i
    {
        let ai: i32 = a@[i];
        s = s + ai;
        proof {
            sum_to_step(a, i);
            assert((s as int) == sum_to(a, i + 1));
        }
        i = i + 1;
    }
    s
}
// </vc-code>

}
fn main() {}