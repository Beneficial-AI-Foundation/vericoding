use vstd::prelude::*;

verus! {

// Helper function to check if a character is a digit (executable version)
fn is_digit(c: char) -> (result: bool)
    ensures result == is_digit_spec(c),
{
    return false;  // TODO: Remove this line and implement the function body
}

// Spec version of is_digit  
spec fn is_digit_spec(c: char) -> bool {
    c >= '0' && c <= '9'
}

// Precondition - trivially true in this case (matches the Lean version)
spec fn all_digits_precond(s: Seq<char>) -> bool {
    true
}

// Main function that checks if all characters in string are digits
fn all_digits(s: &Vec<char>) -> (result: bool)
    requires all_digits_precond(s@),
    ensures all_digits_postcond(s@, result),
{
    return false;  // TODO: Remove this line and implement the function body
}

// Postcondition specification (matches the Lean postcondition)
spec fn all_digits_postcond(s: Seq<char>, result: bool) -> bool {
    result == (forall|i: int| 0 <= i < s.len() ==> is_digit_spec(s[i]))
}

// Theorem that shows the specification is satisfied
// Since all_digits has ensures all_digits_postcond(s@, result), 
// this theorem is automatically satisfied
proof fn all_digits_spec_satisfied(s: Vec<char>)
    requires all_digits_precond(s@)
    // The postcondition is guaranteed by the ensures clause of all_digits
{
    // Trivially true - the function's ensures clause guarantees the postcondition
}

} // verus!

fn main() {
    // TODO: Remove this comment and implement the function body
}