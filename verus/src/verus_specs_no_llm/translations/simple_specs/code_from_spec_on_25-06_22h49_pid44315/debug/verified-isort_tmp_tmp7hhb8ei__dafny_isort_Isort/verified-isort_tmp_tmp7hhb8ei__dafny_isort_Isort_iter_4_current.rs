use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Helper function to demonstrate the sorted spec works
fn check_sorted_example() -> (result: bool)
    ensures result == true
{
    let seq1: Seq<u32> = seq![1u32, 2u32, 3u32, 4u32, 5u32];
    assert(sorted(seq1));
    
    let seq2: Seq<u32> = seq![1u32];
    assert(sorted(seq2));
    
    let seq3: Seq<u32> = seq![];
    assert(sorted(seq3));
    
    true
}

// Proof function to verify properties of sorted sequences
proof fn lemma_sorted_empty()
    ensures sorted(seq![])
{
    // Empty sequence is trivially sorted - no pairs to check
    let empty_seq: Seq<u32> = seq![];
    assert(sorted(empty_seq));
}

proof fn lemma_sorted_single(x: u32)
    ensures sorted(seq![x])
{
    // Single element sequence is trivially sorted
    let single_seq: Seq<u32> = seq![x];
    assert(sorted(single_seq));
}

proof fn lemma_sorted_transitive(a: Seq<u32>)
    requires sorted(a)
    ensures forall|i: int, j: int, k: int| 
        0 <= i < j < k < a.len() ==> a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k]
{
    // The transitivity property follows directly from the sorted property
    // and the transitivity of the <= relation on u32
}

// Additional helper proof functions to establish key properties
proof fn lemma_sorted_prefix(a: Seq<u32>, len: int)
    requires sorted(a)
    requires 0 <= len <= a.len()
    ensures sorted(a.subrange(0, len))
{
    let prefix = a.subrange(0, len);
    assert forall|i: int, j: int| 0 <= i < j < prefix.len() implies prefix[i] <= prefix[j] by {
        assert(prefix[i] == a[i]);
        assert(prefix[j] == a[j]);
        assert(0 <= i < j < len);
        assert(len <= a.len());
        assert(0 <= i < j < a.len());
    }
}

proof fn lemma_sorted_suffix(a: Seq<u32>, start: int)
    requires sorted(a)
    requires 0 <= start <= a.len()
    ensures sorted(a.subrange(start, a.len() as int))
{
    let suffix = a.subrange(start, a.len() as int);
    assert forall|i: int, j: int| 0 <= i < j < suffix.len() implies suffix[i] <= suffix[j] by {
        assert(suffix[i] == a[start + i]);
        assert(suffix[j] == a[start + j]);
        assert(0 <= start + i < start + j < a.len());
    }
}

// Proof that concatenating two sorted sequences where all elements of first <= all elements of second results in sorted sequence
proof fn lemma_sorted_concat(a: Seq<u32>, b: Seq<u32>)
    requires sorted(a)
    requires sorted(b)
    requires forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] <= b[j]
    ensures sorted(a + b)
{
    let concat = a + b;
    assert forall|i: int, j: int| 0 <= i < j < concat.len() implies concat[i] <= concat[j] by {
        if i < a.len() && j < a.len() {
            // Both indices in first sequence
            assert(concat[i] == a[i]);
            assert(concat[j] == a[j]);
        } else if i >= a.len() && j >= a.len() {
            // Both indices in second sequence
            assert(concat[i] == b[i - a.len()]);
            assert(concat[j] == b[j - a.len()]);
            assert(0 <= i - a.len() < j - a.len() < b.len());
        } else {
            // i in first sequence, j in second sequence
            assert(i < a.len() && j >= a.len());
            assert(concat[i] == a[i]);
            assert(concat[j] == b[j - a.len()]);
            assert(0 <= i < a.len());
            assert(0 <= j - a.len() < b.len());
        }
    }
}

}