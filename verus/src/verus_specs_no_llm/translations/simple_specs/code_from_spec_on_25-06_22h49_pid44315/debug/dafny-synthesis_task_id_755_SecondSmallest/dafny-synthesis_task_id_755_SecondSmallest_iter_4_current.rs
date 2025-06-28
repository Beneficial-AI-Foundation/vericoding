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

// Helper spec function to check if a value is the second smallest
spec fn is_second_smallest(s: Seq<int>, min_val: int, second_val: int) -> bool {
    second_val != min_val &&
    (exists|i: int| 0 <= i < s.len() && s[i] == second_val) &&
    (forall|j: int| 0 <= j < s.len() && s[j] != min_val ==> s[j] >= second_val)
}

fn SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires
        s.len() >= 2,
        // There must be at least 2 different values
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) != s.spec_index(j)
    ensures
        // The result exists in the sequence and is not the minimum
        exists|idx: int| 0 <= idx < s.len() && s.spec_index(idx) == secondSmallest,
        // The result is the smallest among all non-minimum values
        forall|k: int| 0 <= k < s.len() && s.spec_index(k) != seq_min(s@) ==> s.spec_index(k) >= secondSmallest,
        // The result is not the minimum
        secondSmallest != seq_min(s@)
{
    let mut minimum = s[0];
    let mut second_min = s[0];
    let mut found_different = false;
    
    // First pass: find the minimum
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() >= 2,
            exists|k: int| 0 <= k < s.len() && s[k] == minimum,
            forall|k: int| 0 <= k < i ==> s[k] >= minimum,
    {
        if s[i] < minimum {
            minimum = s[i];
        }
        i = i + 1;
    }
    
    // Establish that minimum is the global minimum
    assert(forall|k: int| 0 <= k < s.len() ==> s[k] >= minimum);
    assert(is_min_value(s@, minimum));
    assert(minimum == seq_min(s@)) by {
        assert(forall|k: int| 0 <= k < s.len() ==> s[k] >= minimum);
        assert(exists|k: int| 0 <= k < s.len() && s[k] == minimum);
    }
    
    // Second pass: find the second smallest (smallest among non-minimum values)
    i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() >= 2,
            minimum == seq_min(s@),
            is_min_value(s@, minimum),
            forall|k: int| 0 <= k < s.len() ==> s[k] >= minimum,
            found_different ==> (
                second_min != minimum &&
                exists|k: int| 0 <= k < s.len() && s[k] == second_min &&
                forall|k: int| 0 <= k < i && s[k] != minimum ==> s[k] >= second_min
            ),
            !found_different ==> forall|k: int| 0 <= k < i ==> s[k] == minimum,
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
            assert(forall|k: int| 0 <= k < s.len() ==> s[k] == minimum);
            // But precondition says there are at least 2 different values
            assert(exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) != s.spec_index(j));
            // This is a contradiction
            assert(false);
        }
    }
    
    // Final assertions to establish postconditions
    assert(second_min != minimum);
    assert(exists|j: int| 0 <= j < s.len() && s[j] == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s[k] != minimum ==> s[k] >= second_min);
    
    // Prove the postconditions
    assert(exists|idx: int| 0 <= idx < s.len() && s.spec_index(idx) == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s.spec_index(k) != seq_min(s@) ==> s.spec_index(k) >= second_min) by {
        assert(minimum == seq_min(s@));
        assert(forall|k: int| 0 <= k < s.len() && s[k] != minimum ==> s[k] >= second_min);
    }
    assert(second_min != seq_min(s@)) by {
        assert(second_min != minimum);
        assert(minimum == seq_min(s@));
    }
    
    second_min
}

}