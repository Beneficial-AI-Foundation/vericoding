use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn derangement(s: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s.spec_index(i) != i
}

// Helper function to demonstrate usage and verification
proof fn test_derangement_properties() {
    // Example: [1, 0] is a derangement of [0, 1]
    let s = seq![1nat, 0nat];
    assert(derangement(s));
    
    // Example: [0, 1] is not a derangement (identity permutation)
    let s2 = seq![0nat, 1nat];
    assert(!derangement(s2));
    
    // Example: [2, 0, 1] is a derangement of [0, 1, 2]
    let s3 = seq![2nat, 0nat, 1nat];
    assert(derangement(s3));
}

// Property: empty sequence is vacuously a derangement
proof fn empty_derangement() {
    let empty_seq: Seq<nat> = seq![];
    assert(derangement(empty_seq));
}

}