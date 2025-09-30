// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_eligible(participations: Seq<int>, k: int) -> int
    decreases participations.len()
{
    if participations.len() == 0 {
        0 as int
    } else {
        (if 5 - participations[0] >= k { 1 as int } else { 0 as int }) + count_eligible(participations.subrange(1, participations.len() as int), k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): boolean predicate for eligibility based on remaining sessions */
fn eligible_u8(p: u8, k: u8) -> bool
{
    if p <= 5u8 {
        let rem: u8 = 5u8 - p;
        rem >= k
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, k: u8, participations: Vec<u8>) -> (result: u8)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): remove failing assertions, add overflow-safe increment, and keep simple loop invariants */
    let len: usize = participations.len();
    let n_usize: usize = n as usize;
    let limit: usize = if len < n_usize { len } else { n_usize };

    let mut i: usize = 0;
    let mut eligible_count: u8 = 0;

    while i < limit
        invariant
            i <= limit,
            limit <= participations.len(),
            (eligible_count as usize) <= i,
        decreases limit - i
    {
        assert(i < participations.len());
        let p: u8 = participations[i];
        if eligible_u8(p, k) {
            if eligible_count < 255u8 {
                eligible_count = eligible_count + 1;
            }
        }
        i = i + 1;
    }

    let result: u8 = eligible_count / 3u8;
    result
}
// </vc-code>


}

fn main() {}