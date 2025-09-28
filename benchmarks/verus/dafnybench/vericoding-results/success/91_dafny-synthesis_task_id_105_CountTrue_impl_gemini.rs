// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_to(a: &[bool], n: int) -> int
    decreases n when 0 <= n <= a.len()
{
    if n <= 0 { 
        0int 
    } else { 
        count_to(a, n - 1) + if a[n - 1] { 1int } else { 0int } 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed type errors in ensures clause */
proof fn lemma_count_to_step(a: &[bool], i: int)
    requires 0 <= i < a.len()
    ensures count_to(a, i + 1) == count_to(a, i) + if a[i] { 1int } else { 0int }
{
}
// </vc-helpers>

// <vc-spec>
fn count_true(a: &[bool]) -> (result: usize)
    ensures result == count_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): re-submitting with fixed helper dependency */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count <= i,
            count as int == count_to(a, i as int),
        decreases a.len() - i
    {
        proof {
            lemma_count_to_step(a, i as int);
        }

        if a[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}