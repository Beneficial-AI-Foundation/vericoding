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
    /* code modified by LLM (iteration 1): Fixed compilation error by replacing iterator-based loop with index-based loop to avoid using non-existent 'produced()' method */
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !is_z_char(s@[j])
        ensures !seq_contains_z(s@)
    {
        let c = s@[i as int];
        if c == 'z' || c == 'Z' {
            return true;
        }
        i += 1;
    }
    false
}

fn main() {}

} // verus!