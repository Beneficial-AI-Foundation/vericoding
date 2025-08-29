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
    let len = s.unicode_len();
    let mut i: usize = 0;
    
    while i < len
        invariant 
            0 <= i <= len,
            len == s@.len(),
            forall|j: int| 0 <= j < i ==> !is_z_char(s@[j])
        decreases len - i
    {
        let c = s.get_char(i);
        if c == 'z' || c == 'Z' {
            proof {
                assert(is_z_char(s@[i as int]));
                assert(seq_contains_z(s@));
            }
            return true;
        }
        i = i + 1;
    }
    
    proof {
        if seq_contains_z(s@) {
            let idx = choose|j: int| 0 <= j < s@.len() && is_z_char(s@[j]);
            assert(0 <= idx < len);
            assert(false); // contradiction with loop invariant
        }
    }
    
    false
}

fn main() {}

} // verus!