use vstd::prelude::*;

verus! {

// Precondition - always true in this case  
spec fn all_characters_same_precond(chars: &Vec<char>) -> bool {
    true
}

// Helper function to check if all pairs in a sequence are equal (pairwise equality)
spec fn pairwise_equal<T>(seq: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < seq.len() && 0 <= j < seq.len() ==> seq[i] == seq[j]
}

// Helper function to check if there exists an element different from the first
spec fn exists_different_from_first<T: PartialEq>(seq: Seq<T>) -> bool {
    seq.len() > 0 && exists|i: int| 1 <= i < seq.len() && #[trigger] seq[i] != seq[0]
}

// Postcondition that matches the Lean specification
spec fn all_characters_same_postcond(chars: &Vec<char>, result: bool) -> bool {
    let char_seq = chars@;
    (result ==> pairwise_equal(char_seq)) &&
    (!result ==> (char_seq.len() != 0 && exists_different_from_first(char_seq)))
}

// Main function that matches the Lean implementation structure
// Corresponds to: match s.toList with | [] => true | c :: cs => cs.all (fun x => x = c)
fn all_characters_same(chars: &Vec<char>) -> (result: bool)
    requires all_characters_same_precond(chars)
    ensures all_characters_same_postcond(chars, result)
{
    if chars.len() == 0 {
        return true;
    }
    
    let first_char = chars[0];
    let mut i = 1;
    
    while i < chars.len()
        invariant 
            0 < chars.len(),
            1 <= i <= chars.len(),
            forall|k: int| 1 <= k < i ==> chars@[k] == chars@[0],
    {
        if chars[i] != first_char {
            return false;
        }
        i += 1;
    }
    
    true
}

}

fn main() {}