use vstd::prelude::*;

verus! {

// Helper function to check if a character is lowercase (spec version)
spec fn is_lower_case(c: char) -> bool {
    'a' <= c && c <= 'z'
}

// Helper function to check if a character is lowercase (exec version)
exec fn is_lower_case_exec(c: char) -> (result: bool)
    ensures
        result == is_lower_case(c),
{
    'a' <= c && c <= 'z'
}

// Helper function to convert lowercase to uppercase
exec fn char_to_upper(c: char) -> (result: char)
    requires
        is_lower_case(c),
    ensures
        result as u32 == (c as u32) - 32,
{
    // Convert using byte arithmetic
    let byte_val = c as u8;
    let upper_byte = byte_val - 32;
    upper_byte as char
}

// Precondition for toUppercase (trivially true in this case)
spec fn to_uppercase_precond(s: Seq<char>) -> bool {
    true
}

// Convert string to uppercase
fn to_uppercase(s: &Vec<char>) -> (result: Vec<char>)
    requires
        to_uppercase_precond(s@),
    ensures
        result.len() == s.len(),
        forall|i: int| #![trigger s@.index(i), result@.index(i)] 0 <= i < s.len() ==> {
            let c = s@.index(i);
            let result_c = result@.index(i);
            if is_lower_case(c) {
                result_c as u32 == (c as u32) - 32
            } else {
                result_c == c
            }
        },
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| #![trigger s@.index(j), result@.index(j)] 0 <= j < i ==> {
                let c = s@.index(j);
                let result_c = result@.index(j);
                if is_lower_case(c) {
                    result_c as u32 == (c as u32) - 32
                } else {
                    result_c == c
                }
            },
        decreases s.len() - i,
    {
        let c = s[i];
        if is_lower_case_exec(c) {
            let upper_c = char_to_upper(c);
            result.push(upper_c);
        } else {
            result.push(c);
        }
        i += 1;
    }
    
    result
}

// Postcondition specification
spec fn to_uppercase_postcond(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() &&
    forall|i: int| #![trigger s.index(i), result.index(i)] 0 <= i < s.len() ==> {
        let c = s.index(i);
        let result_c = result.index(i);
        if is_lower_case(c) {
            result_c as u32 == (c as u32) - 32
        } else {
            result_c == c
        }
    }
}

fn main() {}

} // verus!