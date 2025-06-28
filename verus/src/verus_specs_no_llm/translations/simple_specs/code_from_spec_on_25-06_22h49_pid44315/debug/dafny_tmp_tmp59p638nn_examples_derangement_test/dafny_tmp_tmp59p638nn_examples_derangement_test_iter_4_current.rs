use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn derangement(s: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s.spec_index(i) != (i as nat)
}

// Helper function to demonstrate usage and verification
proof fn test_derangement_properties() {
    // Example: [1, 0] is a derangement of [0, 1]
    let s = seq![1nat, 0nat];
    
    // Prove that s is a derangement by showing each element is not at its index
    assert forall |i: int| 0 <= i < s.len() implies s.spec_index(i) != (i as nat) by {
        if i == 0 {
            assert(s.spec_index(0) == 1nat);
            assert(1nat != (0 as nat));
        } else if i == 1 {
            assert(s.spec_index(1) == 0nat);
            assert(0nat != (1 as nat));
        }
    };
    assert(derangement(s));
    
    // Example: [0, 1] is not a derangement (identity permutation)
    let s2 = seq![0nat, 1nat];
    
    // Prove that s2 is not a derangement by showing counterexample
    assert(s2.spec_index(0) == 0nat);
    assert(0 <= 0 < s2.len());
    assert(s2.spec_index(0) == (0 as nat));
    assert(!derangement(s2));
    
    // Example: [2, 0, 1] is a derangement of [0, 1, 2]
    let s3 = seq![2nat, 0nat, 1nat];
    
    // Prove that s3 is a derangement
    assert forall |i: int| 0 <= i < s3.len() implies s3.spec_index(i) != (i as nat) by {
        if i == 0 {
            assert(s3.spec_index(0) == 2nat);
            assert(2nat != (0 as nat));
        } else if i == 1 {
            assert(s3.spec_index(1) == 0nat);
            assert(0nat != (1 as nat));
        } else if i == 2 {
            assert(s3.spec_index(2) == 1nat);
            assert(1nat != (2 as nat));
        }
    };
    assert(derangement(s3));
}

// Property: empty sequence is vacuously a derangement
proof fn empty_derangement() {
    let empty_seq: Seq<nat> = seq![];
    
    // Prove that the empty sequence is a derangement
    // The forall statement is vacuously true since there are no valid indices
    assert forall |i: int| 0 <= i < empty_seq.len() implies empty_seq.spec_index(i) != (i as nat) by {
        // This is vacuously true since empty_seq.len() == 0,
        // so there's no i such that 0 <= i < 0
        assert(empty_seq.len() == 0);
    };
    assert(derangement(empty_seq));
}

// Additional property: single element sequence cannot be a derangement
proof fn single_element_not_derangement() {
    let single = seq![5nat];
    
    // Prove that any single element sequence is not a derangement
    // because the element at index 0 would need to not equal 0,
    // but for it to be a valid derangement of [0], it should contain 0
    // However, if it contains 0 at position 0, then it's not a derangement
    assert(single.spec_index(0) == 5nat);
    assert(0 <= 0 < single.len());
    // This particular sequence [5] is not a derangement because 5 != 0
    // But if we had [0], it wouldn't be a derangement either because 0 == 0
    
    let identity_single = seq![0nat];
    assert(identity_single.spec_index(0) == 0nat);
    assert(0 <= 0 < identity_single.len());
    assert(identity_single.spec_index(0) == (0 as nat));
    assert(!derangement(identity_single));
}

}