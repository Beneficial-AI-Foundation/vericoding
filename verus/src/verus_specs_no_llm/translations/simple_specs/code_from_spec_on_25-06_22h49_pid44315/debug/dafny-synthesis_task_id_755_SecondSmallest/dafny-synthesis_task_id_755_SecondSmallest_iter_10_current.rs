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
        assert(s[0] == seq_min(s));
    } else {
        // Recursive case
        let rest = s.subrange(1, s.len() as int);
        lemma_seq_min_properties(rest);
        let rest_min = seq_min(rest);
        
        if s[0] <= rest_min {
            // seq_min(s) == s[0]
            assert(seq_min(s) == s[0]);
        } else {
            // seq_min(s) == rest_min
            assert(seq_min(s) == rest_min);
            // Need to show rest_min exists in original sequence
            assert(exists|i: int| 1 <= i < s.len() && s[i] == rest_min) by {
                assert(exists|i: int| 0 <= i < rest.len() && rest[i] == rest_min);
                let j = choose|i: int| 0 <= i < rest.len() && rest[i] == rest_min;
                assert(s[j + 1] == rest_min);
                assert(s[j + 1] == seq_min(s));
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
    
    // First pass: find the minimum
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            s.len() >= 2,
            exists|k: int| 0 <= k < s.len() && s@[k] == minimum,
            forall|k: int| 0 <= k < i ==> s@[k] >= minimum,
        decreases s.len() - i
    {
        if s[i] < minimum {
            minimum = s[i];
        }
        i = i + 1;
    }
    
    // Prove minimum equals seq_min
    assert(minimum == seq_min(s@)) by {
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= minimum);
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == minimum);
        
        // seq_min is also <= all elements and exists in sequence
        assert(forall|k: int| 0 <= k < s.len() ==> s@[k] >= seq_min(s@));
        assert(exists|k: int| 0 <= k < s.len() && s@[k] == seq_min(s@));
        
        // Both are minimal, so they must be equal
        assert(minimum <= seq_min(s@));
        assert(seq_min(s@) <= minimum);
    }
    
    // Find first non-minimum value to initialize second_min
    i = 0;
    let mut found_second = false;
    while i < s.len() && !found_second
        invariant
            0 <= i <= s.len(),
            minimum == seq_min(s@),
            !found_second ==> forall|k: int| 0 <= k < i ==> s@[k] == minimum,
            found_second ==> (second_min != minimum && exists|k: int| 0 <= k < s.len() && s@[k] == second_min),
        decreases s.len() - i
    {
        if s[i] != minimum {
            second_min = s[i];
            found_second = true;
        }
        i = i + 1;
    }
    
    // At this point, found_second must be true due to precondition
    assert(found_second) by {
        if !found_second {
            assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == minimum);
            // This contradicts the precondition that there are at least 2 different values
            let witness_i = choose|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j];
            let witness_j = choose|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j];
            assert(s@[witness_i.0] != s@[witness_j.1]);
            assert(s@[witness_i.0] == minimum);
            assert(s@[witness_j.1] == minimum);
            assert(false);
        }
    }
    
    // Continue to find the true second minimum
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            minimum == seq_min(s@),
            second_min != minimum,
            exists|k: int| 0 <= k < s.len() && s@[k] == second_min,
            forall|k: int| 0 <= k < i && s@[k] != minimum ==> s@[k] >= second_min,
        decreases s.len() - i
    {
        if s[i] != minimum && s[i] < second_min {
            second_min = s[i];
        }
        i = i + 1;
    }
    
    // Establish final postconditions
    assert(second_min != seq_min(s@)) by {
        assert(second_min != minimum);
        assert(minimum == seq_min(s@));
    }
    assert(exists|idx: int| 0 <= idx < s.len() && s@[idx] == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s@[k] != seq_min(s@) ==> s@[k] >= second_min) by {
        assert(forall|k: int| 0 <= k < s.len() && s@[k] != minimum ==> s@[k] >= second_min);
        assert(minimum == seq_min(s@));
    }
    
    second_min
}

}