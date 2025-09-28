use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn less_than_threshold(threshold: int) -> spec_fn(int) -> bool {
    |i: int| i < threshold
}

proof fn lemma_set_filter_finite(s: Set<int>, threshold: int)
    requires s.finite(),
    ensures s.filter(less_than_threshold(threshold)).finite(),
{
    assert(s.filter(less_than_threshold(threshold)).subset_of(s));
}

proof fn lemma_count_matches_filter(s: Set<int>, threshold: int, count: nat)
    requires 
        s.finite(),
        count == s.to_seq().filter(less_than_threshold(threshold)).len(),
    ensures count == s.filter(less_than_threshold(threshold)).len(),
{
    let filtered_set = s.filter(less_than_threshold(threshold));
    let seq = s.to_seq();
    let filtered_seq = seq.filter(less_than_threshold(threshold));
    
    assert(filtered_set.finite()) by {
        lemma_set_filter_finite(s, threshold);
    }
    
    assert(filtered_seq.to_set() =~= filtered_set) by {
        assert forall |x: int| filtered_seq.to_set().contains(x) <==> filtered_set.contains(x) by {
            if filtered_seq.to_set().contains(x) {
                assert(filtered_seq.contains(x));
                assert(seq.contains(x));
                assert(s.contains(x));
                assert(x < threshold);
                assert(filtered_set.contains(x));
            }
            if filtered_set.contains(x) {
                assert(s.contains(x));
                assert(x < threshold);
                assert(seq.contains(x));
                assert(filtered_seq.contains(x));
                assert(filtered_seq.to_set().contains(x));
            }
        }
    }
    
    assert(filtered_seq.len() == filtered_set.len());
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    let seq = numbers.to_seq();
    let filtered_seq = seq.filter(less_than_threshold(threshold));
    let count = filtered_seq.len();
    
    proof {
        lemma_count_matches_filter(numbers, threshold, count);
    }
    
    count as usize
}
// </vc-code>

fn main() {}

}