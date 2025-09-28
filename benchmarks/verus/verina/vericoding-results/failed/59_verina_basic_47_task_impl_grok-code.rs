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
spec fn sum_to_seq(s: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to_seq(s, n - 1) + (s[n - 1] as int) }
} /* helper modified by LLM (iteration 5): fixed as_seq usage in code to use @ instead */
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed i to usize and used a@ for sequence view */
    let mut sum = 0i32;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len() as int,
            (sum as int) == sum_to_seq(a@, i as int),
        decreases a.len() - i
    {
        proof {
            assert(sum_to_seq(a@, (i + 1) as int) == sum_to_seq(a@, i as int) + (a[i] as int)) by {
                reveal(sum_to_seq);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}