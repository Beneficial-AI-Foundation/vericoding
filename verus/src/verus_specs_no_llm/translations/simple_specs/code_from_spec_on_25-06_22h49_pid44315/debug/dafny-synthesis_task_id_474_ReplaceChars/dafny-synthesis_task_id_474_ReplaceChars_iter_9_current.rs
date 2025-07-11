use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceChars(s: String, oldChar: char, newChar: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s@.index(i) == oldChar ==> v@.index(i) == newChar) && (s@.index(i) != oldChar ==> v@.index(i) == s@.index(i))
{
    let mut result_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let s_view = s.as_str();
    let s_chars: Vec<char> = s_view.chars().collect();
    
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_chars.len() == s.len(),
            result_chars.len() == i,
            forall |j: int| 0 <= j < s_chars.len() ==> s_chars@.index(j) == s@.index(j),
            forall |j: int| 0 <= j < i ==> (s@.index(j) == oldChar ==> result_chars@.index(j) == newChar) && (s@.index(j) != oldChar ==> result_chars@.index(j) == s@.index(j))
    {
        let ch = s_chars[i];
        
        if ch == oldChar {
            result_chars.push(newChar);
        } else {
            result_chars.push(ch);
        }
        
        i += 1;
    }
    
    let result = convert_chars_to_string(result_chars);
    
    proof {
        assert(result.len() == result_chars.len());
        assert(result_chars.len() == s_chars.len());
        assert(s_chars.len() == s.len());
        assert(result.len() == s.len());
        
        assert forall |k: int| 0 <= k < s.len() implies 
            (s@.index(k) == oldChar ==> result@.index(k) == newChar) && 
            (s@.index(k) != oldChar ==> result@.index(k) == s@.index(k))
        by {
            assert(result@.index(k) == result_chars@.index(k));
            assert(s@.index(k) == s_chars@.index(k));
        }
    }
    
    result
}

fn convert_chars_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall |i: int| 0 <= i < chars.len() ==> result@.index(i) == chars@.index(i)
{
    let mut result_string = String::new();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            result_string.len() == i,
            forall |j: int| 0 <= j < i ==> result_string@.index(j) == chars@.index(j)
    {
        result_string.push(chars[i]);
        i += 1;
    }
    
    result_string
}

}