use vstd::prelude::*;

verus! {

// Helper function to check if a character is space, comma, or dot (spec version)
spec fn is_space_comma_dot_spec(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// Helper function to check if a character is space, comma, or dot (exec version)
fn is_space_comma_dot(c: char) -> (result: bool)
    ensures result == is_space_comma_dot_spec(c)
{
    return false;  // TODO: Remove this line and implement the function body
}

// Precondition - always true in this case
spec fn replace_with_colon_precond(s: Seq<char>) -> bool {
    true
}

// Postcondition specification
spec fn replace_with_colon_postcond(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() &&
    forall|i: int| #![trigger s.index(i)] #![trigger result.index(i)] 
        0 <= i < s.len() ==> {
            let old_char = s.index(i);
            let new_char = result.index(i);
            if is_space_comma_dot_spec(old_char) {
                new_char == ':'
            } else {
                new_char == old_char
            }
        }
}

// Main function that replaces spaces, commas, and dots with colons
fn replace_with_colon(s: &Vec<char>) -> (result: Vec<char>)
    requires replace_with_colon_precond(s@)
    ensures replace_with_colon_postcond(s@, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {
    // TODO: Remove this comment and implement the function body
}