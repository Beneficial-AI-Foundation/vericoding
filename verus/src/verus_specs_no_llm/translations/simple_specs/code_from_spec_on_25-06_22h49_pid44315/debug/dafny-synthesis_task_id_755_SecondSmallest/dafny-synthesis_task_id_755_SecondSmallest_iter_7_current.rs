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
        // Base case is trivial
    } else {
        // Recursive case
        let rest = s.subrange(1, s.len() as int);
        lemma_seq_min_properties(rest);
        let rest_min = seq_min(rest);
        
        if s[0] <= rest_min {
            // seq_min(s) == s[0]
        } else {
            // seq_min(s) == rest_min
            // Need to show rest_min exists in original sequence
            assert(exists|i: int| 1 <= i < s.len() && s[i] == rest_min) by {
                assert(exists|i: int| 0 <= i < rest.len() && rest[i] == rest_min);
                let j = choose|i: int| 0 <= i < rest.len() && rest[i] == rest_min;
                assert(s[j + 1] == rest_min);
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
    
    // Prove minimum equals seq_min
    proof {
        lemma_seq_min_properties(s@);
        // minimum is <= all elements and exists in sequence
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum);
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == minimum);
        
        // seq_min is also <= all elements and exists in sequence
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= seq_min(s@));
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == seq_min(s@));
        
        // Both are minimal, so they must be equal
        assert(minimum <= seq_min(s@)); // since minimum <= all elements
        assert(seq_min(s@) <= minimum); // since seq_min <= all elements
    }
    
    // Find first non-minimum value to initialize second_min
    i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            minimum == seq_min(s@),
            forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum,
            forall|k: int| 0 <= k < i ==> s@[k] == minimum,
    {
        if s[i] != minimum {
            second_min = s[i];
            found_different = true;
            break;
        }
        i = i + 1;
    }
    
    // At this point, if found_different is false, all elements are minimum
    // But precondition guarantees at least 2 different values exist
    assert(found_different) by {
        if !found_different {
            assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == minimum);
            // This contradicts the precondition
            assert(exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j]);
            assert(false);
        }
    }
    
    // Continue from where we left off to find the true second minimum
    i = i + 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            minimum == seq_min(s@),
            second_min != minimum,
            exists|k: int| 0 <= k < s.len() && s@[k] == second_min,
            forall|k: int| 0 <= k < i && s@[k] != minimum ==> s@[k] >= second_min,
    {
        if s[i] != minimum && s[i] < second_min {
            second_min = s[i];
        }
        i = i + 1;
    }
    
    // Establish final postconditions
    assert(second_min != seq_min(s@));
    assert(exists|idx: int| 0 <= idx < s.len() && s@[idx] == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s@[k] != seq_min(s@) ==> s@[k] >= second_min);
    
    second_min
}

}