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
    assert(sorted(seq1)) by {
        // Prove that seq1 is sorted
        assert forall|i: int, j: int| 0 <= i < j < seq1.len() implies seq1[i] <= seq1[j] by {
            // For each pair (i,j) with 0 <= i < j < 5, verify seq1[i] <= seq1[j]
            if i == 0 && j == 1 { assert(seq1[i] == 1u32 && seq1[j] == 2u32); }
            if i == 0 && j == 2 { assert(seq1[i] == 1u32 && seq1[j] == 3u32); }
            if i == 0 && j == 3 { assert(seq1[i] == 1u32 && seq1[j] == 4u32); }
            if i == 0 && j == 4 { assert(seq1[i] == 1u32 && seq1[j] == 5u32); }
            if i == 1 && j == 2 { assert(seq1[i] == 2u32 && seq1[j] == 3u32); }
            if i == 1 && j == 3 { assert(seq1[i] == 2u32 && seq1[j] == 4u32); }
            if i == 1 && j == 4 { assert(seq1[i] == 2u32 && seq1[j] == 5u32); }
            if i == 2 && j == 3 { assert(seq1[i] == 3u32 && seq1[j] == 4u32); }
            if i == 2 && j == 4 { assert(seq1[i] == 3u32 && seq1[j] == 5u32); }
            if i == 3 && j == 4 { assert(seq1[i] == 4u32 && seq1[j] == 5u32); }
        }
    };
    
    let seq2: Seq<u32> = seq![1u32];
    assert(sorted(seq2)) by {
        // Single element sequence is trivially sorted
        assert forall|i: int, j: int| 0 <= i < j < seq2.len() implies seq2[i] <= seq2[j] by {
            // No pairs exist since seq2.len() == 1
        }
    };
    
    let seq3: Seq<u32> = seq![];
    assert(sorted(seq3)) by {
        // Empty sequence is trivially sorted
        assert forall|i: int, j: int| 0 <= i < j < seq3.len() implies seq3[i] <= seq3[j] by {
            // No pairs exist since seq3.len() == 0
        }
    };
    
    true
}

// Proof function to verify properties of sorted sequences
proof fn lemma_sorted_empty()
    ensures sorted(seq![])
{
    // Empty sequence is trivially sorted - no pairs to check
    let empty_seq: Seq<u32> = seq![];
    assert forall|i: int, j: int| 0 <= i < j < empty_seq.len() implies empty_seq[i] <= empty_seq[j] by {
        // Since empty_seq.len() == 0, the condition 0 <= i < j < 0 is never satisfied
    }
}

proof fn lemma_sorted_single(x: u32)
    ensures sorted(seq![x])
{
    // Single element sequence is trivially sorted
    let single_seq: Seq<u32> = seq![x];
    assert forall|i: int, j: int| 0 <= i < j < single_seq.len() implies single_seq[i] <= single_seq[j] by {
        // Since single_seq.len() == 1, we need 0 <= i < j < 1
        // This means i == 0 and j must be < 1, but j > i, so no valid pairs exist
    }
}

proof fn lemma_sorted_transitive(a: Seq<u32>)
    requires sorted(a)
    ensures forall|i: int, j: int, k: int| 
        0 <= i < j < k < a.len() ==> a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k]
{
    // Follows from the definition of sorted and transitivity of <=
    assert forall|i: int, j: int, k: int| 0 <= i < j < k < a.len() implies 
        a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k] by {
        // From sorted(a), we know a[i] <= a[j] and a[j] <= a[k]
        // By transitivity of <=, we get a[i] <= a[k]
    }
}

}