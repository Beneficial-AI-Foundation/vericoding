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
/* helper modified by LLM (iteration 5): Add lemma_count_matches_nonnegative helper */
proof fn lemma_count_matches_nonnegative(xs: Seq<u64>, x: u64)
    ensures
        count_matches(xs, x) >= 0,
    decreases xs.len()
{
    if xs.len() > 0 {
        lemma_count_matches_nonnegative(xs.skip(1), x);
    }
}

proof fn lemma_count_matches_head(xs: Seq<u64>, x: u64)
    requires
        xs.len() > 0,
    ensures
        count_matches(xs, x) == (if xs[0] == x { 1int } else { 0int }) + count_matches(xs.skip(1), x),
    decreases xs.len()
{
}

proof fn lemma_count_matches_cons(y: u64, xs: Seq<u64>, x: u64)
    ensures
        count_matches(Seq::new(1, |i| y).add(xs), x) == (if y == x { 1int } else { 0int }) + count_matches(xs, x),
    decreases xs.len()
{
}

proof fn lemma_count_take_filter_equality(xs: Seq<u64>, i: int, candidate: u64)
    requires
        0 <= i <= xs.len(),
    ensures
        count_matches(xs.take(i), candidate) == count_matches(xs.take(i as int), candidate),
{
}

proof fn lemma_count_matches_pos_implies_exists(xs: Seq<u64>, x: u64)
    requires
        count_matches(xs, x) > 0,
    ensures
        exists|i: int| 0 <= i < xs.len() && xs[i] == x,
    decreases xs.len()
{
    if xs.len() == 0 {
    } else {
        if xs[0] == x {
        } else {
            lemma_count_matches_pos_implies_exists(xs.skip(1), x);
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
/* code modified by LLM (iteration 5): Fix missing lemma_count_matches_nonnegative function call */
{
    let n: usize = xs.len();
    let mut candidate = xs[0];
    let mut count: usize = 1;
    
    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            count >= 0,
            exists|x: u64| count_matches(xs@, x) > n / 2,
            (forall|x: u64| count_matches(xs@.take(i as int), x) <= count_matches(xs@.take(i as int), candidate)),
            count_matches(xs@.take(i as int), candidate) > i / 2,
            count == count_matches(xs@.take(i as int), candidate) - count_matches(xs@.take(i as int).filter(|v: u64| v != candidate), candidate),
        decreases n - i
    {
        if count == 0 {
            candidate = xs[i];
            count = 1;
        } else if xs[i] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
        i += 1;
    }
    
    proof {
        lemma_count_matches_nonnegative(xs@, candidate);
        assert(count_matches(xs@, candidate) > n / 2);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}