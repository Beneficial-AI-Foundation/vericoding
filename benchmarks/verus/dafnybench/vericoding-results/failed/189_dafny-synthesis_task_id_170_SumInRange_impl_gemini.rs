// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends 
        0 <= start <= end <= a.len(),
    decreases end
    when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        sum_to(a, start, end - 1) + a[end - 1]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed lemma causing compilation error to use axiom directly */
// </vc-helpers>

// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use axiom_seq_map_get to prove property of map and fix compilation error */
{
    let mut sum: i32 = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            sum as int == sum_to(a@.map(|idx, v| v as int), start as int, i as int),
        decreases end - i
    {
        proof {
            vstd::axioms::axiom_seq_map_get(a@, |_, v| v as int, i as int);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}