use vstd::prelude::*;

verus! {

// Check if a character is an uppercase alphabet letter
pub fn is_upper_alpha(c: char) -> (result: bool)
{
    'A' <= c && c <= 'Z'
}

// Check if a character is a lowercase alphabet letter  
pub fn is_lower_alpha(c: char) -> (result: bool)
{
    'a' <= c && c <= 'z'
}

// Determine if a character is alphabetic
pub fn is_alpha(c: char) -> (result: bool)
{
    is_upper_alpha(c) || is_lower_alpha(c)
}

// Convert a single character to lowercase
pub fn to_lower(c: char) -> (result: char)
{
    if is_upper_alpha(c) {
        match c {
            'A' => 'a', 'B' => 'b', 'C' => 'c', 'D' => 'd', 'E' => 'e', 'F' => 'f',
            'G' => 'g', 'H' => 'h', 'I' => 'i', 'J' => 'j', 'K' => 'k', 'L' => 'l',
            'M' => 'm', 'N' => 'n', 'O' => 'o', 'P' => 'p', 'Q' => 'q', 'R' => 'r',
            'S' => 's', 'T' => 't', 'U' => 'u', 'V' => 'v', 'W' => 'w', 'X' => 'x',
            'Y' => 'y', 'Z' => 'z',
            _ => c,
        }
    } else {
        c
    }
}

// Normalize a character: keep only lowercase letters
pub fn normalize_char(c: char) -> (result: Option<char>)
{
    if is_alpha(c) {
        Some(to_lower(c))
    } else {
        None
    }
}

// Normalize a string into a vector of lowercase alphabetic characters
pub fn normalize_string(s: &str) -> (result: Vec<char>)
{
    let mut norm: Vec<char> = Vec::new();
    let chars = s.chars();
    for c in chars {
        match normalize_char(c) {
            Some(c_norm) => {
                norm.push(c_norm);
            },
            None => {}
        }
    }
    norm
}

// Check if two vectors are equal element-wise
pub fn vec_equal(v1: &Vec<char>, v2: &Vec<char>) -> (result: bool)
    ensures result == (v1@ =~= v2@)
{
    if v1.len() != v2.len() {
        return false;
    }
    
    let mut i = 0;
    while i < v1.len()
        invariant 
            0 <= i <= v1.len(),
            v1.len() == v2.len(),
            forall|j: int| 0 <= j < i ==> v1[j] == v2[j],
        decreases v1.len() - i
    {
        if v1[i] != v2[i] {
            return false;
        }
        i += 1;
    }
    true
}

// Reverse the vector
pub fn reverse_vec(xs: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == xs@.reverse()
{
    let mut rev = Vec::new();
    let mut i = xs.len();
    while i > 0
        invariant 
            0 <= i <= xs.len(),
            rev.len() == xs.len() - i,
            forall|j: int| 0 <= j < rev.len() ==> rev[j] == xs[xs.len() - 1 - j],
        decreases i
    {
        i = i - 1;
        rev.push(xs[i]);
    }
    rev
}

pub open spec fn is_clean_palindrome_precond(s: &str) -> bool
{
    true
}

pub fn is_clean_palindrome(s: &str) -> (result: bool)
    requires is_clean_palindrome_precond(s)
{
    let norm = normalize_string(s);
    let rev_norm = reverse_vec(&norm);
    vec_equal(&norm, &rev_norm)
}

// Postcondition expressed directly in terms of the result
pub open spec fn is_clean_palindrome_postcond(s: &str, result: bool, norm_seq: Seq<char>) -> bool
{
    (result == true ==> (norm_seq =~= norm_seq.reverse())) && 
    (result == false ==> !(norm_seq =~= norm_seq.reverse()))
}

} // verus!

fn main() {}