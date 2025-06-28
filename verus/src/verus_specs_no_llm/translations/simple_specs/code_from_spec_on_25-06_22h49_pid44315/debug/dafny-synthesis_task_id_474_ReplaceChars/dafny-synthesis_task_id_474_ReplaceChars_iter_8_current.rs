use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceChars(s: String, oldChar: char, newChar: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.spec_index(i) == oldChar ==> v.spec_index(i) == newChar) && (s.spec_index(i) != oldChar ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result_chars.len() == i,
            forall |j: int| 0 <= j < i ==> (s.spec_index(j) == oldChar ==> result_chars[j] == newChar) && (s.spec_index(j) != oldChar ==> result_chars[j] == s.spec_index(j))
    {
        let ch = s.spec_index(i as int);
        
        if ch == oldChar {
            result_chars.push(newChar);
        } else {
            result_chars.push(ch);
        }
        
        i += 1;
    }
    
    let result = convert_chars_to_string(result_chars);
    result
}

fn convert_chars_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall |i: int| 0 <= i < chars.len() ==> result.spec_index(i) == chars[i]
{
    let mut result_string = String::new();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            result_string.len() == i,
            forall |j: int| 0 <= j < i ==> result_string.spec_index(j) == chars[j]
    {
        result_string.push(chars[i]);
        i += 1;
    }
    
    result_string
}

}