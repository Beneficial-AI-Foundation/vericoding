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
proof fn lemma_count_matches_split(xs: Seq<u64>, x: u64, i: int)
    requires
        0 <= i <= xs.len() as int,
    ensures
        count_matches(xs, x) == count_matches(xs.subrange(0, i), x) + count_matches(xs.subrange(i, xs.len() as int), x),
    decreases xs.len()
{
    /* helper modified by LLM (iteration 5): Complete recursive proof with proper base cases */
    if xs.len() == 0 {
        assert(xs.subrange(0, 0) =~= Seq::empty());
        assert(xs.subrange(0, 0) =~= Seq::empty());
    } else if i == 0 {
        assert(xs.subrange(0, 0) =~= Seq::empty());
        assert(xs.subrange(0, xs.len() as int) =~= xs);
    } else if i == xs.len() as int {
        assert(xs.subrange(xs.len() as int, xs.len() as int) =~= Seq::empty());
        assert(xs.subrange(0, xs.len() as int) =~= xs);
    } else {
        let xs_tail = xs.skip(1);
        lemma_count_matches_split(xs_tail, x, i - 1);
        assert(xs_tail.subrange(0, i - 1) =~= xs.subrange(1, i));
        assert(xs_tail.subrange(i - 1, xs_tail.len() as int) =~= xs.subrange(i, xs.len() as int));
        assert(count_matches(xs, x) == 
            (if xs[0] == x {1} else {0}) + count_matches(xs_tail, x));
        assert(count_matches(xs_tail, x) == 
            count_matches(xs.subrange(1, i), x) + count_matches(xs.subrange(i, xs.len() as int), x));
        assert(count_matches(xs.subrange(0, i), x) == 
            (if xs[0] == x {1} else {0}) + count_matches(xs.subrange(1, i), x));
    }
}

proof fn lemma_count_matches_nonnegative(xs: Seq<u64>, x: u64)
    ensures
        count_matches(xs, x) >= 0,
    decreases xs.len()
{
    /* helper modified by LLM (iteration 5): Simple non-negativity proof */
    if xs.len() > 0 {
        lemma_count_matches_nonnegative(xs.skip(1), x);
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
    /* code modified by LLM (iteration 5): Fixed loop invariants, count handling, and postcondition proof */
    let mut candidate = xs[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count >= 0,
            count_matches(xs@.subrange(0, i as int), candidate) == count as nat,
            count_matches(xs@.subrange(0, i as int), candidate) > (i as int - count as int) / 2,
        decreases xs.len() - i
    {
        if count == 0 {
            candidate = xs[i];
            count = 1;
        } else if xs[i] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_count_matches_nonnegative(xs@, candidate);
        lemma_count_matches_split(xs@, candidate, i as int);
        assert(count_matches(xs@, candidate) == 
            count_matches(xs@.subrange(0, i as int), candidate) + 
            count_matches(xs@.subrange(i as int, xs.len() as int), candidate));
        assert(count_matches(xs@.subrange(0, i as int), candidate) == count as nat);
        assert(count_matches(xs@.subrange(0, i as int), candidate) > (xs.len() as int) / 2);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}