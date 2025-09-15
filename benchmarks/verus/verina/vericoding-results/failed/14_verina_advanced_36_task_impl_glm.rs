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
spec fn contains_majority_element(xs: Seq<u64>) -> bool {
    exists|x: u64| count_matches(xs, x) > xs.len() / 2
}

proof fn count_matches_skip_first(xs: Seq<u64>, x: u64)
    requires contains_majority_element(xs),
    ensures count_matches(xs.skip(1), x) == count_matches(xs, x) - (if xs[0] == x { 1 } else { 0 }),
{
    if xs.len() == 0 {
        assert(true);
    } else {
        assert(xs.skip(1).len() == xs.len() - 1);
        assert(forall|i: int| 0 <= i < xs.skip(1).len() ==> xs.skip(1)[i] == xs[i + 1]);
    }
}

spec fn find_first_candidate(xs: Seq<u64>) -> u64
    decreases xs.len(),
{
    if xs.len() == 0 {
        arbitrary()
    } else {
        let rest = xs.skip(1);
        if rest.len() == 0 {
            xs[0]
        } else {
            if count_matches(rest, xs[0]) > rest.len() / 2 {
                xs[0]
            } else {
                let first_non_match = rest.index_of(|y| y != xs[0]);
                if first_non_match is Some {
                    find_first_candidate(rest.skip(first_non_match.unwrap() + 1))
                } else {
                    xs[0]
                }
            }
        }
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
{
    /* code modified by LLM (iteration 2): fixed syntax error in loop invariants */
    let mut candidate = xs[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < xs.len()
        invariant 0 <= i <= xs.len(),
        invariant count >= 0,
        invariant count <= i,
        invariant count == 0 ==> !contains_majority_element(xs@.subrange(0, i as int)),
        invariant count > 0 ==> count_matches(xs@.subrange(0, i as int), candidate) == count,
    {
        if xs[i] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
            if count == 0 && i + 1 < xs.len() {
                candidate = xs[i + 1];
                count = 1;
                i = i + 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(count_matches(xs@, candidate) > xs.len() / 2);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}