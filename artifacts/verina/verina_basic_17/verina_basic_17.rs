use vstd::prelude::*;

verus! {

// Helper function to check if a character is uppercase
spec fn is_upper_case(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

// Exec version of is_upper_case
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    'A' <= c && c <= 'Z'
}

// Helper function to shift character by 32 (convert uppercase to lowercase)
spec fn shift32(c: char) -> char {
    if c == 'A' { 'a' } else if c == 'B' { 'b' } else if c == 'C' { 'c' } else if c == 'D' { 'd' } else if c == 'E' { 'e' }
    else if c == 'F' { 'f' } else if c == 'G' { 'g' } else if c == 'H' { 'h' } else if c == 'I' { 'i' } else if c == 'J' { 'j' }
    else if c == 'K' { 'k' } else if c == 'L' { 'l' } else if c == 'M' { 'm' } else if c == 'N' { 'n' } else if c == 'O' { 'o' }
    else if c == 'P' { 'p' } else if c == 'Q' { 'q' } else if c == 'R' { 'r' } else if c == 'S' { 's' } else if c == 'T' { 't' }
    else if c == 'U' { 'u' } else if c == 'V' { 'v' } else if c == 'W' { 'w' } else if c == 'X' { 'x' } else if c == 'Y' { 'y' }
    else if c == 'Z' { 'z' } else { c }
}

// Executable version of shift32
fn shift32_exec(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == shift32(c)
{
    match c {
        'A' => 'a', 'B' => 'b', 'C' => 'c', 'D' => 'd', 'E' => 'e',
        'F' => 'f', 'G' => 'g', 'H' => 'h', 'I' => 'i', 'J' => 'j',
        'K' => 'k', 'L' => 'l', 'M' => 'm', 'N' => 'n', 'O' => 'o',
        'P' => 'p', 'Q' => 'q', 'R' => 'r', 'S' => 's', 'T' => 't',
        'U' => 'u', 'V' => 'v', 'W' => 'w', 'X' => 'x', 'Y' => 'y',
        'Z' => 'z',
        _ => c,
    }
}

// Precondition (always true in the original Lean code)
spec fn to_lowercase_precond(chars: &Vec<char>) -> bool {
    true
}

// Convert Vec<char> to lowercase
fn to_lowercase(chars: &Vec<char>) -> (result: Vec<char>)
    requires to_lowercase_precond(chars)
    ensures
        // Length preservation
        result.len() == chars.len(),
        // Character transformation property
        forall |i: int| 0 <= i < chars.len() ==> 
            #[trigger] chars[i] == chars[i] ==> {
                if is_upper_case(chars[i]) {
                    result[i] == shift32(chars[i])
                } else {
                    result[i] == chars[i]
                }
            }
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> 
                #[trigger] chars[j] == chars[j] ==> {
                    if is_upper_case(chars[j]) {
                        result[j] == shift32(chars[j])
                    } else {
                        result[j] == chars[j]
                    }
                }
        decreases chars.len() - i
    {
        let c = chars[i];
        if is_upper_case_exec(c) {
            result.push(shift32_exec(c));
        } else {
            result.push(c);
        }
        i += 1;
    }
    
    result
}

// Postcondition specification
spec fn to_lowercase_postcond(chars: &Vec<char>, result: &Vec<char>) -> bool {
    result.len() == chars.len() &&
    forall |i: int| 0 <= i < chars.len() ==> {
        if is_upper_case(chars[i]) {
            result[i] == shift32(chars[i])
        } else {
            result[i] == chars[i]
        }
    }
}

fn main() {}

} // verus!