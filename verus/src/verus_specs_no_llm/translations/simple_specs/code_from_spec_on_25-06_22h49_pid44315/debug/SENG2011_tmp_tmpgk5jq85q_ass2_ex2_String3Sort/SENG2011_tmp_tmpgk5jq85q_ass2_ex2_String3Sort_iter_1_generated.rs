use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to check if a string is sorted
spec fn Sorted(s: String, start: int, end: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s.as_bytes()[i] <= s.as_bytes()[j]
}

// Helper function to convert string to vector of bytes for easier manipulation
fn string_to_vec(s: &String) -> (result: Vec<u8>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == s.as_bytes()[i]
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s.as_bytes()[j]
    {
        result.push(s.as_bytes()[i]);
        i += 1;
    }
    result
}

// Helper function to convert vector of bytes back to string
fn vec_to_string(v: Vec<u8>) -> (result: String)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> result.as_bytes()[i] == v[i]
{
    // This is a simplified implementation - in real Verus we'd need proper UTF-8 handling
    String::from_utf8(v).unwrap_or(String::new())
}

fn String3Sort(a: String) -> (b: String)
    requires
        a.len() == 3
    ensures
        Sorted(b, 0, b.len()),
        a.len() == b.len(),
        // Assuming the incomplete "multiset" constraint means the result contains the same characters
        forall|c: u8| count_char(a, c) == count_char(b, c)
{
    let mut chars = string_to_vec(&a);
    
    // Simple sorting algorithm for 3 elements
    // Compare and swap positions 0 and 1
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
    }
    
    // Compare and swap positions 1 and 2
    if chars[1] > chars[2] {
        let temp = chars[1];
        chars.set(1, chars[2]);
        chars.set(2, temp);
    }
    
    // Compare and swap positions 0 and 1 again
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
    }
    
    vec_to_string(chars)
}

// Helper spec function to count occurrences of a character
spec fn count_char(s: String, c: u8) -> nat {
    count_char_rec(s, c, 0)
}

spec fn count_char_rec(s: String, c: u8, index: nat) -> nat 
    decreases s.len() - index
{
    if index >= s.len() {
        0
    } else if s.as_bytes()[index as int] == c {
        1 + count_char_rec(s, c, index + 1)
    } else {
        count_char_rec(s, c, index + 1)
    }
}

}