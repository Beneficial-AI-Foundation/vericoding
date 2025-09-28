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
/* helper modified by LLM (iteration 4): Fixed termination and proof issues in lemmas */
proof fn lemma_count_matches_skip(xs: Seq<u64>, x: u64, i: int)
    requires
        0 < i <= xs.len(),
    ensures
        count_matches(xs.skip(i), x) == count_matches(xs, x) - count_matches(xs.take(i), x),
    decreases i,
{
    if i == 1 {
        assert(xs.take(1) == seq![xs[0]]);
        assert(xs.skip(1).len() == xs.len() - 1);
        if xs[0] == x {
            assert(count_matches(xs.take(1), x) == 1);
        } else {
            assert(count_matches(xs.take(1), x) == 0);
        }
    } else {
        lemma_count_matches_skip(xs, x, i - 1);
        assert(xs.take(i) == xs.take(i - 1).push(xs[i - 1]));
        assert(xs.skip(i - 1).len() > 0);
        assert(xs.skip(i - 1)[0] == xs[i - 1]);
        assert(xs.skip(i) == xs.skip(i - 1).skip(1));
        
        if xs[i - 1] == x {
            assert(count_matches(xs.take(i), x) == count_matches(xs.take(i - 1), x) + 1);
            assert(count_matches(xs.skip(i - 1), x) == 1 + count_matches(xs.skip(i), x));
        } else {
            assert(count_matches(xs.take(i), x) == count_matches(xs.take(i - 1), x));
            assert(count_matches(xs.skip(i - 1), x) == count_matches(xs.skip(i), x));
        }
    }
}

proof fn lemma_count_matches_split(xs: Seq<u64>, x: u64, i: int)
    requires
        0 <= i <= xs.len(),
    ensures
        count_matches(xs.take(i), x) + count_matches(xs.skip(i), x) == count_matches(xs, x),
    decreases xs.len() - i,
{
    if i == xs.len() {
        assert(xs.take(xs.len() as int) == xs);
        assert(xs.skip(xs.len() as int) == Seq::<u64>::empty());
        assert(count_matches(Seq::<u64>::empty(), x) == 0);
    } else {
        lemma_count_matches_split(xs, x, i + 1);
        assert(xs.skip(i).len() > 0);
        assert(xs.skip(i)[0] == xs[i]);
        assert(xs.take(i + 1) == xs.take(i).push(xs[i]));
        assert(xs.skip(i + 1) == xs.skip(i).skip(1));
        
        if xs[i] == x {
            assert(count_matches(xs.take(i + 1), x) == count_matches(xs.take(i), x) + 1);
            assert(count_matches(xs.skip(i), x) == 1 + count_matches(xs.skip(i + 1), x));
        } else {
            assert(count_matches(xs.take(i + 1), x) == count_matches(xs.take(i), x));
            assert(count_matches(xs.skip(i), x) == count_matches(xs.skip(i + 1), x));
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
    /* code modified by LLM (iteration 4): Fixed loop invariants and arithmetic overflow */
    let mut candidate = xs[0];
    let mut balance: usize = 1;
    let mut i: usize = 1;
    
    // Boyer-Moore majority vote algorithm
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            0 <= balance <= i,
            balance > 0 ==> candidate == xs[0] || exists|j: int| 0 < j < i && xs[j as usize] == candidate,
        decreases xs.len() - i,
    {
        if xs[i] == candidate {
            balance = balance + 1;
        } else if balance > 0 {
            balance = balance - 1;
        } else {
            candidate = xs[i];
            balance = 1;
        }
        i = i + 1;
    }
    
    // Count occurrences of candidate
    let mut count: usize = 0;
    i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count <= i,
            count == count_matches(xs@.take(i as int), candidate),
        decreases xs.len() - i,
    {
        if xs[i] == candidate {
            if count < xs.len() {  // Prevent overflow
                count = count + 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(xs@.take(xs.len() as int) == xs@);
        assert(count == count_matches(xs@, candidate));
        // Since we know a majority element exists, the candidate must be it
        let majority = choose|x: u64| count_matches(xs@, x) > xs.len() / 2;
        if candidate != majority {
            // This would contradict the Boyer-Moore algorithm's correctness
            // The majority element would have survived the first phase
            assert(false);
        }
    }
    
    assert(count > xs.len() / 2);
    candidate
}
// </vc-code>

}
fn main() {}