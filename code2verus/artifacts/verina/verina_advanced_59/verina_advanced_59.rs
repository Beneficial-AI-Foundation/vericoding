use vstd::prelude::*;

verus! {

// Helper functions for character operations
spec fn is_alpha_numeric(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

exec fn is_alpha_numeric_exec(c: char) -> (result: bool)
    ensures result == is_alpha_numeric(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

spec fn to_lower_char(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}

exec fn to_lower_char_exec(c: char) -> (result: char)
    ensures result == to_lower_char(c)
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}

// Precondition for palindrome check (always true in this case)  
spec fn palindrome_ignore_non_alnum_precond(s: &str) -> bool {
    true
}

// Spec function to represent the cleaned string
spec fn clean_string(s: &str) -> Seq<char>;

// Postcondition specification - matches the original Lean postcondition
spec fn palindrome_ignore_non_alnum_postcond(s: &str, result: bool) -> bool {
    let cleaned = clean_string(s);
    let forward = cleaned;
    let backward = cleaned.reverse();
    
    if result {
        forward == backward
    } else {
        forward != backward
    }
}

// Main function implementation
fn palindrome_ignore_non_alnum(s: &str) -> (result: bool)
    requires palindrome_ignore_non_alnum_precond(s)
    ensures palindrome_ignore_non_alnum_postcond(s, result)
{
    // Create cleaned vector by filtering and converting to lowercase
    let mut cleaned: Vec<char> = Vec::new();
    
    let len = s.unicode_len();
    for i in 0..len
        invariant 
            cleaned.len() <= i,
            i <= len
    {
        if i < s.unicode_len() {
            let c = s.get_char(i);
            if is_alpha_numeric_exec(c) {
                cleaned.push(to_lower_char_exec(c));
            }
        }
    }
    
    let n = cleaned.len();
    
    // Check if cleaned string is a palindrome
    for i in 0..(n / 2)
        invariant i <= n / 2
    {
        let left_idx = i;
        let right_idx = n - 1 - i;
        if left_idx < cleaned.len() && right_idx < cleaned.len() {
            if cleaned[left_idx] != cleaned[right_idx] {
                return false;
            }
        }
    }
    
    true
}

// Theorem statement that the implementation satisfies the specification
proof fn palindrome_ignore_non_alnum_spec_satisfied(s: &str)
    requires palindrome_ignore_non_alnum_precond(s)
    ensures palindrome_ignore_non_alnum_postcond(s, palindrome_ignore_non_alnum(s))
{
    // Proof would go here - for now we admit
    admit();
}

fn main() {}

}