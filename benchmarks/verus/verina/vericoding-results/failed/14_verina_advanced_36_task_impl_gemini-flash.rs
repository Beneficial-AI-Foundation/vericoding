// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_matches(xs: Seq<u64>, x: u64) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let first_match: nat = if xs[0] == x { 1 } else { 0 };
        first_match + count_matches(xs.skip(1), x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes were applied to the helper function. */
proof fn lemma_count_matches_append_one(s: Seq<u64>, x: u64, y: u64)
    ensures
        count_matches(s.push(y), x) == count_matches(s, x) + if y == x { 1nat } else { 0nat }
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_matches(s.push(y), x) == count_matches(s, x) + if y == x { 1nat } else { 0nat });
    } else {
        lemma_count_matches_append_one(s.skip(1), x, y);
        assert(count_matches(s.push(y), x) == (if s[0] == x { 1nat } else { 0nat }) + count_matches(s.skip(1).push(y), x));
    }
}
// </vc-helpers>

// <vc-spec>
fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires 
        xs.len() > 0,
        exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
    ensures
        count_matches(xs@, result) > xs.len() / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added a decreases clause to the `while` loop. */
{
    let mut candidate: u64 = 0;
    let mut count: u64 = 0;

    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i,
            i <= xs.len()
        decreases xs.len() - i
    {
        let x = xs[i];
        if count == 0 {
            candidate = x;
            count = 1;
        } else if candidate == x {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    candidate
}
// </vc-code>

}
fn main() {}