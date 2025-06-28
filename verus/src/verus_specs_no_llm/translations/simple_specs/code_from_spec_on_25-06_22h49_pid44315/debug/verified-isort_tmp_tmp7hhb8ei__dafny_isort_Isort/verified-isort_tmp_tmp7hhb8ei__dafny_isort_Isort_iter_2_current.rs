use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Helper function to demonstrate the sorted spec works
fn check_sorted_example() -> (result: bool)
    ensures result == true
{
    let seq1: Seq<nat> = seq![1nat, 2nat, 3nat, 4nat, 5nat];
    assert(sorted(seq1));
    
    let seq2: Seq<nat> = seq![1nat];
    assert(sorted(seq2));
    
    let seq3: Seq<nat> = seq![];
    assert(sorted(seq3));
    
    true
}

// Proof function to verify properties of sorted sequences
proof fn lemma_sorted_empty()
    ensures sorted(seq![])
{
    // Empty sequence is trivially sorted
}

proof fn lemma_sorted_single(x: nat)
    ensures sorted(seq![x])
{
    // Single element sequence is trivially sorted
}

proof fn lemma_sorted_transitive(a: Seq<nat>)
    requires sorted(a)
    ensures forall|i: int, j: int, k: int| 
        0 <= i < j < k < a.len() ==> a[i] <= a[j] && a[j] <= a[k] && a[i] <= a[k]
{
    // Follows from the definition of sorted and transitivity of <=
}

}