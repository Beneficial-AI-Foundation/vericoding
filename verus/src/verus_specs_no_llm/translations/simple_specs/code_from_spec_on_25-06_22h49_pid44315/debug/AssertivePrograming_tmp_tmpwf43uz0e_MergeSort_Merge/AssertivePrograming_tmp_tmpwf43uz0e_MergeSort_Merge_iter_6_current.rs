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
}

proof fn lemma_single_element_is_sorted(x: int)
    ensures Sorted(seq![x])
{
}

proof fn lemma_sorted_subsequence(q: Seq<int>, start: int, end: int)
    requires Sorted(q)
    requires 0 <= start <= end <= q.len()
    ensures Sorted(q.subrange(start, end))
{
}

}