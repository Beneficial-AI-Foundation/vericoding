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
    assert(empty_seq.len() == 0);
    assert(sorted(empty_seq)) by {
        assert forall|i: int, j: int| 0 <= i < j < empty_seq.len() implies empty_seq[i] <= empty_seq[j] by {
            // This is vacuously true since empty_seq.len() == 0
            // No valid i, j exist such that 0 <= i < j < 0
        }
    }
}

proof fn lemma_sorted_single(x: u32)
    ensures sorted(seq![x])
{
    // Single element sequence is trivially sorted
    let single_seq: Seq<u32> = seq![x];
    assert(single_seq.len() == 1);
    assert(sorted(single_seq)) by {
        assert forall|i: int, j: int| 0 <= i < j < single_seq.len() implies single_seq[i] <= single_seq[j] by {
            // This is vacuously true since there are no valid i, j with 0 <= i < j < 1
            // The only possible values are i=0, but then j must be >= 1, which violates j < 1
        }
    }
}

proof fn lemma_sorted_transitive(a: Seq<u32>)
    requires sorted(a)
    ensures forall|i: int, j: int, k: int| 
        0 <= i < j < k < a.len() ==> a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k]
{
    // The transitivity property follows directly from the sorted property
    assert forall|i: int, j: int, k: int| 0 <= i < j < k < a.len() implies 
        a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k] by {
        // From the constraint 0 <= i < j < k < a.len(), we can derive:
        assert(0 <= i < j < a.len()); // from i < j < k < a.len()
        assert(0 <= j < k < a.len()); // from i < j < k < a.len()
        assert(0 <= i < k < a.len()); // from i < j < k < a.len()
        
        // Apply sorted property to get individual comparisons
        assert(a[i] <= a[j]); // from sorted(a) with i < j
        assert(a[j] <= a[k]); // from sorted(a) with j < k  
        assert(a[i] <= a[k]); // from sorted(a) with i < k
    }
}

// Additional helper proof functions to establish key properties
proof fn lemma_sorted_prefix(a: Seq<u32>, len: int)
    requires sorted(a)
    requires 0 <= len <= a.len()
    ensures sorted(a.subrange(0, len))
{
    let prefix = a.subrange(0, len);
    assert(prefix.len() == len);
    assert forall|i: int, j: int| 0 <= i < j < prefix.len() implies prefix[i] <= prefix[j] by {
        // prefix[i] corresponds to a[0 + i] = a[i]
        // prefix[j] corresponds to a[0 + j] = a[j]
        assert(prefix[i] == a[i]);
        assert(prefix[j] == a[j]);
        // Since 0 <= i < j < prefix.len() = len <= a.len()
        // We have 0 <= i < j < a.len()
        assert(0 <= i < j < a.len());
        // From sorted(a), we get a[i] <= a[j]
        assert(a[i] <= a[j]);
    }
}

proof fn lemma_sorted_suffix(a: Seq<u32>, start: int)
    requires sorted(a)
    requires 0 <= start <= a.len()
    ensures sorted(a.subrange(start, a.len() as int))
{
    let suffix = a.subrange(start, a.len() as int);
    assert(suffix.len() == a.len() - start);
    assert forall|i: int, j: int| 0 <= i < j < suffix.len() implies suffix[i] <= suffix[j] by {
        // suffix[i] corresponds to a[start + i]
        // suffix[j] corresponds to a[start + j]
        assert(suffix[i] == a[start + i]);
        assert(suffix[j] == a[start + j]);
        // Since 0 <= i < j < suffix.len() and suffix.len() = a.len() - start
        // We have start <= start + i < start + j < a.len()
        assert(start + i < start + j);
        assert(start + j < start + suffix.len());
        assert(start + suffix.len() == a.len());
        assert(0 <= start + i < start + j < a.len());
        // From sorted(a), we get a[start + i] <= a[start + j]
        assert(a[start + i] <= a[start + j]);
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
    assert(concat.len() == a.len() + b.len());
    assert forall|i: int, j: int| 0 <= i < j < concat.len() implies concat[i] <= concat[j] by {
        if i < a.len() && j < a.len() {
            // Both indices in first sequence
            assert(concat[i] == a[i]);
            assert(concat[j] == a[j]);
            // From sorted(a) and 0 <= i < j < a.len(), we get a[i] <= a[j]
            assert(0 <= i < j < a.len());
            assert(a[i] <= a[j]);
        } else if i >= a.len() && j >= a.len() {
            // Both indices in second sequence
            let i_in_b = i - a.len();
            let j_in_b = j - a.len();
            assert(concat[i] == b[i_in_b]);
            assert(concat[j] == b[j_in_b]);
            // Since i < j, we have i_in_b < j_in_b
            assert(i_in_b == i - a.len());
            assert(j_in_b == j - a.len());
            assert(i_in_b < j_in_b); // because i < j
            assert(0 <= i_in_b < j_in_b < b.len());
            // From sorted(b), we get b[i_in_b] <= b[j_in_b]
            assert(b[i_in_b] <= b[j_in_b]);
        } else {
            // i in first sequence, j in second sequence (i < a.len() && j >= a.len())
            assert(i < a.len() && j >= a.len());
            let j_in_b = j - a.len();
            assert(concat[i] == a[i]);
            assert(concat[j] == b[j_in_b]);
            assert(0 <= i < a.len());
            assert(0 <= j_in_b < b.len());
            // From the cross-sequence requirement: a[i] <= b[j_in_b]
            assert(a[i] <= b[j_in_b]);
        }
    }
}

}