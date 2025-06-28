use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function is valid
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| (0 <= i && i <= j && j < q.len()) ==> (q.spec_index(i) <= q.spec_index(j))
}

// Adding some helper functions to demonstrate the Sorted predicate works
proof fn lemma_empty_seq_is_sorted()
    ensures Sorted(Seq::<int>::empty())
{
    // An empty sequence is trivially sorted because there are no pairs of indices to check
    assert forall|i: int, j: int| (0 <= i && i <= j && j < Seq::<int>::empty().len()) ==> 
        (Seq::<int>::empty().spec_index(i) <= Seq::<int>::empty().spec_index(j)) by {
        // The condition (0 <= i && i <= j && j < 0) is always false since len() = 0
        let empty_seq = Seq::<int>::empty();
        assert(empty_seq.len() == 0);
        // Since j < 0 is impossible when j >= 0, the premise is false, making implication vacuously true
    };
}

proof fn lemma_single_element_is_sorted(x: int)
    ensures Sorted(seq![x])
{
    let s = seq![x];
    assert(s.len() == 1);
    assert forall|i: int, j: int| (0 <= i && i <= j && j < s.len()) ==> 
        (s.spec_index(i) <= s.spec_index(j)) by {
        // For a single element sequence, len() = 1
        // The only valid indices are i = 0, j = 0
        if 0 <= i && i <= j && j < s.len() {
            assert(j < 1);
            assert(i >= 0 && i <= j && j < 1);
            assert(i == 0 && j == 0);
            assert(s.spec_index(0) == x);
            assert(x <= x);
        }
    };
}

proof fn lemma_sorted_subsequence(q: Seq<int>, start: int, end: int)
    requires Sorted(q)
    requires 0 <= start <= end <= q.len()
    ensures Sorted(q.subrange(start, end))
{
    let sub = q.subrange(start, end);
    
    assert forall|i: int, j: int| (0 <= i && i <= j && j < sub.len()) ==> 
        (sub.spec_index(i) <= sub.spec_index(j)) by {
        if 0 <= i && i <= j && j < sub.len() {
            // Key insight: subrange maps indices
            // sub.spec_index(k) == q.spec_index(start + k) for valid k
            
            // Establish the relationship between sub and original sequence indices
            let orig_i = start + i;
            let orig_j = start + j;
            
            // Prove that orig_i and orig_j are valid indices in q and maintain order
            assert(0 <= orig_i) by {
                assert(start >= 0 && i >= 0);
            }
            assert(orig_i <= orig_j) by {
                assert(i <= j);
            }
            assert(orig_j < q.len()) by {
                assert(j < sub.len());
                assert(sub.len() == end - start);
                assert(j < end - start);
                assert(orig_j == start + j < start + (end - start) == end);
                assert(end <= q.len());
            }
            
            // Now we can apply the Sorted property of q
            assert(q.spec_index(orig_i) <= q.spec_index(orig_j));
            
            // And connect this back to the subsequence
            assert(sub.spec_index(i) == q.spec_index(orig_i));
            assert(sub.spec_index(j) == q.spec_index(orig_j));
            assert(sub.spec_index(i) <= sub.spec_index(j));
        }
    };
}

}