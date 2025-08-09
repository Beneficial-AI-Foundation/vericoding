use vstd::prelude::*;

verus! {

// Helper function to check if a character is a digit
spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

// Count digits in a character sequence
spec fn count_digits_chars(chars: Seq<char>) -> nat 
    decreases chars.len()
{
    if chars.len() == 0 {
        0
    } else {
        let rest_count = count_digits_chars(chars.drop_first());
        if is_digit(chars[0]) {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

// Precondition for countDigits - always true in this case  
spec fn count_digits_precond(s: &str) -> bool {
    true
}

// Postcondition specification matching the original Lean structure
spec fn count_digits_postcond(s: &str, result: nat) -> bool {
    let digit_count = count_digits_chars(s@);
    result == digit_count && digit_count == result
}

// Main function that counts digits in a string
fn count_digits(s: &str) -> (result: usize)
    requires count_digits_precond(s),
    ensures count_digits_postcond(s, result as nat),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): cast s@.len() to usize for type compatibility */
    while i < s@.len() as usize
        invariant 
            i <= s@.len(),
            count as nat == count_digits_chars(s@.take(i as int)),
    {
        let c = s.as_bytes()[i] as char;
        if '0' <= c && c <= '9' {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        /* code modified by LLM (iteration 1): updated assertion to use s@.len() */
        assert(s@.take(s@.len() as int) == s@);
    }
    
    count
}

// Theorem equivalent to the Lean proof
proof fn count_digits_spec_satisfied(s: &str)
    requires count_digits_precond(s),
    ensures count_digits_postcond(s, count_digits_chars(s@)),
{
    // The postcondition is tautological: it states that 
    // count_digits_chars(s@) == count_digits_chars(s@) && count_digits_chars(s@) == count_digits_chars(s@)
    // This is trivially true by reflexivity of equality
}

} // verus!

fn main() {}