use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to find minimum value in a sequence
spec fn seq_min(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = seq_min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

// Helper spec function to check if a value is the minimum in the sequence
spec fn is_min_value(s: Seq<int>, val: int) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == val) &&
    (forall|j: int| 0 <= j < s.len() ==> s[j] >= val)
}

// Lemma to prove properties about seq_min
proof fn lemma_seq_min_properties(s: Seq<int>)
    requires s.len() > 0
    ensures 
        exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s),
        forall|j: int| 0 <= j < s.len() ==> s[j] >= seq_min(s),
    decreases s.len()
{
    if s.len() == 1 {
        // Base case
        assert(s[0] == seq_min(s));
        assert(exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s));
        assert(forall|j: int| 0 <= j < s.len() ==> s[j] >= seq_min(s));
    } else {
        // Recursive case
        let rest = s.subrange(1, s.len() as int);
        lemma_seq_min_properties(rest);
        let rest_min = seq_min(rest);
        
        if s[0] <= rest_min {
            assert(seq_min(s) == s[0]);
            assert(exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s));
            assert(forall|j: int| 0 <= j < s.len() ==> s[j] >= seq_min(s)) by {
                assert(forall|j: int| 1 <= j < s.len() ==> s[j] >= rest_min);
                assert(s[0] <= rest_min);
                assert(forall|j: int| 1 <= j < s.len() ==> s[j] >= s[0]);
            }
        } else {
            assert(seq_min(s) == rest_min);
            assert(exists|i: int| 1 <= i < s.len() && s[i] == rest_min);
            assert(exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s));
            assert(forall|j: int| 0 <= j < s.len() ==> s[j] >= seq_min(s)) by {
                assert(forall|j: int| 1 <= j < s.len() ==> s[j] >= rest_min);
                assert(s[0] > rest_min);
            }
        }
    }
}

fn SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires
        s.len() >= 2,
        // There must be at least 2 different values
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j]
    ensures
        // The result exists in the sequence and is not the minimum
        exists|idx: int| 0 <= idx < s.len() && s@[idx] == secondSmallest,
        // The result is the smallest among all non-minimum values
        forall|k: int| 0 <= k < s.len() && s@[k] != seq_min(s@) ==> s@[k] >= secondSmallest,
        // The result is not the minimum
        secondSmallest != seq_min(s@)
{
    proof {
        lemma_seq_min_properties(s@);
    }
    
    let mut minimum = s[0];
    let mut second_min = s[0];
    let mut found_different = false;
    
    // First pass: find the minimum
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() >= 2,
            exists|k: int| 0 <= k < s.len() && s@[k] == minimum,
            forall|k: int| 0 <= k < i ==> s@[k] >= minimum,
    {
        if s[i] < minimum {
            minimum = s[i];
        }
        i = i + 1;
    }
    
    // Establish that minimum is the global minimum
    assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum);
    assert(is_min_value(s@, minimum));
    
    proof {
        lemma_seq_min_properties(s@);
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == seq_min(s@));
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= seq_min(s@));
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum);
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == minimum);
        
        // Since minimum is <= all elements and seq_min is <= all elements,
        // and both exist in the sequence, they must be equal
        assert(minimum >= seq_min(s@));
        assert(seq_min(s@) >= minimum);
        assert(minimum == seq_min(s@));
    }
    
    // Second pass: find the second smallest (smallest among non-minimum values)
    i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() >= 2,
            minimum == seq_min(s@),
            is_min_value(s@, minimum),
            forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum,
            found_different ==> (
                second_min != minimum &&
                exists|k: int| 0 <= k < s.len() && s@[k] == second_min &&
                forall|k: int| 0 <= k < i && s@[k] != minimum ==> s@[k] >= second_min
            ),
            !found_different ==> forall|k: int| 0 <= k < i ==> s@[k] == minimum,
    {
        if s[i] != minimum {
            if !found_different {
                second_min = s[i];
                found_different = true;
            } else if s[i] < second_min {
                second_min = s[i];
            }
        }
        i = i + 1;
    }
    
    // Prove that found_different must be true based on precondition
    assert(found_different) by {
        if !found_different {
            // If found_different is false, then all elements equal minimum
            assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == minimum);
            // But precondition says there are at least 2 different values
            assert(exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j]);
            // This is a contradiction
            assert(false);
        }
    }
    
    // Final assertions to establish postconditions
    assert(second_min != minimum);
    assert(exists|j: int| 0 <= j < s.len() && s@[j] == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s@[k] != minimum ==> s@[k] >= second_min);
    
    // Prove the postconditions
    assert(exists|idx: int| 0 <= idx < s.len() && s@[idx] == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s@[k] != seq_min(s@) ==> s@[k] >= second_min) by {
        assert(minimum == seq_min(s@));
        assert(forall|k: int| 0 <= k < s.len() && s@[k] != minimum ==> s@[k] >= second_min);
    }
    assert(second_min != seq_min(s@)) by {
        assert(second_min != minimum);
        assert(minimum == seq_min(s@));
    }
    
    second_min
}

}