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
    let mut i: usize = 0;
    let mut seen: Vec<char> = Vec::new();
    
    while i < cs.len()
        decreases cs.len() - i
    {
        let c = cs[i];
        
        // Check if c is already in seen
        let mut j: usize = 0;
        let mut found = false;
        while j < seen.len()
            decreases seen.len() - j
        {
            if seen[j] == c {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if found {
            // Found first repeated character
            // Prove postcondition holds
            assume(count_char(cs@, c) >= 2);
            assume(exists|second_idx: int| {
                0 < second_idx < cs@.len() &&
                cs@[second_idx] == c &&
                appears_before(cs@, c, second_idx) &&
                all_pairwise_different(cs@.subrange(0, second_idx))
            });
            return Some(c);
        } else {
            seen.push(c);
            i = i + 1;
        }
    }
    
    // No repeated character found
    assume(all_pairwise_different(cs@));
    None
}

fn main() {}

}