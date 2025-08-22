use vstd::prelude::*;

verus! {

// Check if all elements in a sequence are pairwise different (no duplicates)
spec fn all_pairwise_different(cs: Seq<char>) -> bool {
    forall|i: int, j: int| 0 <= i < cs.len() && 0 <= j < cs.len() && i != j ==> cs[i] != cs[j]
}

// Count occurrences of character in sequence
spec fn count_char(cs: Seq<char>, c: char) -> nat {
    cs.filter(|x: char| x == c).len()
}

// Check if character c appears in the first n positions of cs
spec fn appears_before(cs: Seq<char>, c: char, n: int) -> bool {
    exists|i: int| 0 <= i < n && i < cs.len() && cs[i] == c
}

// Precondition (always true - no restrictions on input)
spec fn find_first_repeated_char_precond(cs: Seq<char>) -> bool {
    true
}

// Postcondition matching the original Lean specification
spec fn find_first_repeated_char_postcond(cs: Seq<char>, result: Option<char>) -> bool {
    match result {
        Some(c) => {
            // Character appears at least twice
            count_char(cs, c) >= 2 &&
            // There exists a second occurrence where all chars before it are unique
            exists|second_idx: int| {
                0 < second_idx < cs.len() &&
                cs[second_idx] == c &&
                appears_before(cs, c, second_idx) &&
                all_pairwise_different(cs.subrange(0, second_idx))
            }
        }
        None => {
            // No character appears twice
            all_pairwise_different(cs)
        }
    }
}

fn find_first_repeated_char(cs: Vec<char>) -> (result: Option<char>)
    requires find_first_repeated_char_precond(cs@)
    ensures find_first_repeated_char_postcond(cs@, result)
{
    let mut seen = Vec::new();
    let mut i = 0;
    
    while i < cs.len()
        invariant
            0 <= i <= cs.len(),
            forall|k: int| 0 <= k < seen.len() ==> exists|j: int| 0 <= j < i && cs@[j] == seen@[k],
            all_pairwise_different(seen@),
            forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < seen.len() && seen@[k] == cs@[j],
            all_pairwise_different(cs@.subrange(0, i))
    {
        let current_char = cs[i];
        
        // Check if we've seen this character before
        let mut found = false;
        let mut j = 0;
        while j < seen.len()
            invariant
                0 <= j <= seen.len(),
                found <==> exists|k: int| 0 <= k < j && seen@[k] == current_char
        {
            if seen[j] == current_char {
                found = true;
                break;
            }
            j += 1;
        }
        
        if found {
            // We found a repeat - this is our answer
            return Some(current_char);
        } else {
            // Add to seen characters
            seen.push(current_char);
        }
        
        i += 1;
    }
    
    // No repeats found
    None
}

fn main() {}

}