use vstd::prelude::*;

verus! {

// Helper function to check if a character is a digit (executable version)
fn is_digit(c: char) -> (result: bool)
    ensures result == is_digit_spec(c),
{
    c >= '0' && c <= '9'
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
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix termination verification */
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_digit_spec(s@[j]),
        decreases s.len() - i
    {
        if !is_digit(s[i]) {
            return false;
        }
        i += 1;
    }
    true
}

// Postcondition specification (matches the Lean postcondition)
spec fn all_digits_postcond(s: Seq<char>, result: bool) -> bool {
    result == (forall|i: int| 0 <= i < s.len() ==> is_digit_spec(s[i]))
}

// Theorem that shows the specification is satisfied
// Since all_digits has ensures all_digits_postcond(s@, result), 
// this theorem is automatically satisfied
/* code modified by LLM (iteration 1): changed from proof fn to regular fn to allow calling exec function all_digits */
fn all_digits_spec_satisfied(s: Vec<char>)
    requires all_digits_precond(s@)
    // The postcondition is guaranteed by the ensures clause of all_digits
{
    let result = all_digits(&s);
    assert(all_digits_postcond(s@, result));
}

} // verus!

fn main() {
    let test_vec = vec!['1', '2', '3'];
    let result = all_digits(&test_vec);
    println!("All digits: {}", result);
}