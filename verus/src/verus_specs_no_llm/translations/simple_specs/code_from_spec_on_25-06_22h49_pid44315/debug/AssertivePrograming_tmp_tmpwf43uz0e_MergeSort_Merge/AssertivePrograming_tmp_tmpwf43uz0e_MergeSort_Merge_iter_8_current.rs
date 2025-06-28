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
        // So the implication is vacuously true
        assert(Seq::<int>::empty().len() == 0);
        assert(!(0 <= i && i <= j && j < 0));
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
        // So we have s[0] <= s[0] which is always true
        if 0 <= i && i <= j && j < s.len() {
            assert(i == 0 && j == 0);
            assert(s.spec_index(i) == x);
            assert(s.spec_index(j) == x);
        }
    };
}

proof fn lemma_sorted_subsequence(q: Seq<int>, start: int, end: int)
    requires Sorted(q)
    requires 0 <= start <= end <= q.len()
    ensures Sorted(q.subrange(start, end))
{
    let sub = q.subrange(start, end);
    assert(sub.len() == end - start);
    
    assert forall|i: int, j: int| (0 <= i && i <= j && j < sub.len()) ==> 
        (sub.spec_index(i) <= sub.spec_index(j)) by {
        if 0 <= i && i <= j && j < sub.len() {
            // sub.spec_index(i) corresponds to q.spec_index(start + i)
            // sub.spec_index(j) corresponds to q.spec_index(start + j)
            assert(sub.spec_index(i) == q.spec_index(start + i));
            assert(sub.spec_index(j) == q.spec_index(start + j));
            
            // Since 0 <= i <= j < sub.len() = end - start
            // We have start <= start + i <= start + j < end <= q.len()
            assert(start + i >= 0);
            assert(start + i <= start + j);
            assert(start + j < start + sub.len());
            assert(start + sub.len() == end);
            assert(start + j < end);
            assert(end <= q.len());
            assert(start + j < q.len());
            
            // By the precondition that q is sorted
            assert(q.spec_index(start + i) <= q.spec_index(start + j));
        }
    };
}

}