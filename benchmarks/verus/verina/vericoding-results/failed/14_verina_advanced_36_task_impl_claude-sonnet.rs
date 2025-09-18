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
/* helper modified by LLM (iteration 5): simplified helpers and removed ghost return from proof */
proof fn count_matches_skip_property(xs: Seq<u64>, x: u64, target: u64)
    requires xs.len() > 0
    ensures count_matches(xs, target) == (if xs[0] == target { 1nat } else { 0nat }) + count_matches(xs.skip(1), target)
{
}

proof fn count_matches_preserves_majority(xs: Seq<u64>, target: u64)
    requires 
        xs.len() > 0,
        count_matches(xs, target) > xs.len() / 2
    ensures count_matches(xs.skip(1), target) >= 0
{
    assert(count_matches(xs, target) >= count_matches(xs.skip(1), target));
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
{
    /* code modified by LLM (iteration 5): removed ghost variable and fixed exec mode */
    let mut candidate = xs[0];
    let mut count: i32 = 1;
    let mut i: usize = 1;
    
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
            count >= 0,
        decreases xs.len() - i
    {
        if xs[i] == candidate {
            count = count + 1;
        } else {
            if count == 0 {
                candidate = xs[i];
                count = 1;
            } else {
                count = count - 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        let majority = choose|x: u64| count_matches(xs@, x) > xs.len() / 2;
        assert(count_matches(xs@, majority) > xs.len() / 2);
        assert(candidate == majority);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}