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
            assert(1nat != 0nat);
        } else if i == 1 {
            assert(s.spec_index(1) == 0nat);
            assert(0nat != 1nat);
        }
    };
    assert(derangement(s));
    
    // Example: [0, 1] is not a derangement (identity permutation)
    let s2 = seq![0nat, 1nat];
    
    // Prove that s2 is not a derangement by showing counterexample
    assert(s2.spec_index(0) == 0nat);
    assert(0 <= 0 < s2.len());
    assert(s2.spec_index(0) == 0nat);
    assert(!derangement(s2));
    
    // Example: [2, 0, 1] is a derangement of [0, 1, 2]
    let s3 = seq![2nat, 0nat, 1nat];
    
    // Prove that s3 is a derangement
    assert forall |i: int| 0 <= i < s3.len() implies s3.spec_index(i) != (i as nat) by {
        if i == 0 {
            assert(s3.spec_index(0) == 2nat);
            assert(2nat != 0nat);
        } else if i == 1 {
            assert(s3.spec_index(1) == 0nat);
            assert(0nat != 1nat);
        } else if i == 2 {
            assert(s3.spec_index(2) == 1nat);
            assert(1nat != 2nat);
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

// Additional property: single element sequence analysis
proof fn single_element_analysis() {
    // For the sequence [5], it is actually a derangement since 5 != 0
    let single = seq![5nat];
    assert(single.spec_index(0) == 5nat);
    assert(0 <= 0 < single.len());
    assert(5nat != 0nat);
    assert(derangement(single));
    
    // Standard case where we have [0] - not a derangement
    let identity_single = seq![0nat];
    assert(identity_single.spec_index(0) == 0nat);
    assert(0 <= 0 < identity_single.len());
    assert(identity_single.spec_index(0) == 0nat);
    assert(!derangement(identity_single));
}

// Additional helper proof to show properties of derangements
proof fn derangement_properties() {
    // Show that [1, 0, 3, 2] is a derangement
    let s = seq![1nat, 0nat, 3nat, 2nat];
    
    assert forall |i: int| 0 <= i < s.len() implies s.spec_index(i) != (i as nat) by {
        if i == 0 {
            assert(s.spec_index(0) == 1nat);
            assert(1nat != 0nat);
        } else if i == 1 {
            assert(s.spec_index(1) == 0nat);
            assert(0nat != 1nat);
        } else if i == 2 {
            assert(s.spec_index(2) == 3nat);
            assert(3nat != 2nat);
        } else if i == 3 {
            assert(s.spec_index(3) == 2nat);
            assert(2nat != 3nat);
        }
    };
    assert(derangement(s));
}

// Additional proof showing a non-derangement case
proof fn non_derangement_example() {
    // Show that [1, 1, 0] is not a derangement (element at index 1 equals index 1)
    let s = seq![1nat, 1nat, 0nat];
    
    // Show counterexample: at index 1, we have value 1
    assert(s.spec_index(1) == 1nat);
    assert(0 <= 1 < s.len());
    assert(s.spec_index(1) == 1nat);
    assert(!derangement(s));
}

}