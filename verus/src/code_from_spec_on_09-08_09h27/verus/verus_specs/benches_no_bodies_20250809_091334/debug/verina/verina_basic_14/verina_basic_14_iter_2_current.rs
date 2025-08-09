use vstd::prelude::*;

verus! {

// Precondition - always true in this case
spec fn contains_z_precond(s: &str) -> bool {
    true
}

// Helper specification function to check if a character is z or Z
spec fn is_z_char(c: char) -> bool {
    c == 'z' || c == 'Z'
}

// Specification function that checks if sequence contains z or Z
spec fn seq_contains_z(chars: Seq<char>) -> bool {
    exists|i: int| 0 <= i < chars.len() && is_z_char(chars[i])
}

// Main function that checks if string contains 'z' or 'Z'
fn contains_z(s: &str) -> (result: bool)
    requires contains_z_precond(s),
    ensures result <==> seq_contains_z(s@)
{    
    /* code modified by LLM (iteration 1): Changed from iterator-based loop to index-based loop to avoid Chars::start() method issue */
    let len = s.unicode_len();
    let mut i: usize = 0;
    
    while i < len
        invariant 
            i <= len,
            forall|j: int| 0 <= j < i ==> !is_z_char(s@[j])
    {
        let c = s.get_char(i);
        if c == 'z' || c == 'Z' {
            /* code modified by LLM (iteration 1): Added proof block to establish postcondition when returning true */
            proof {
                assert(is_z_char(s@[i as int]));
                assert(exists|k: int| 0 <= k < s@.len() && is_z_char(s@[k]));
            }
            return true;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): Added proof block to establish postcondition when returning false */
    proof {
        assert(forall|j: int| 0 <= j < s@.len() ==> !is_z_char(s@[j]));
        assert(!seq_contains_z(s@));
    }
    false
}

fn main() {}

} // verus!