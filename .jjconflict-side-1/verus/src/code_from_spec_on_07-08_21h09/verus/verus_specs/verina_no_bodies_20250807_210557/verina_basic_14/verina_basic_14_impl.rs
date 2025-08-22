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
    /* code modified by LLM (iteration 2): Fixed compilation error by using proper executable code with chars() iterator instead of ghost sequence operations */
    let ghost s_seq = s@;
    let mut i: usize = 0;
    
    for c in s.chars()
        invariant 
            0 <= i <= s_seq.len(),
            forall|j: int| 0 <= j < i ==> !is_z_char(s_seq[j]),
            i == s_seq.len() ==> forall|j: int| 0 <= j < s_seq.len() ==> !is_z_char(s_seq[j])
    {
        if c == 'z' || c == 'Z' {
            proof {
                assert(is_z_char(c));
                assert(c == s_seq[i as int]);
                assert(seq_contains_z(s_seq));
            }
            return true;
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s_seq.len() ==> !is_z_char(s_seq[j]));
        assert(!seq_contains_z(s_seq));
    }
    false
}

fn main() {}

} // verus!