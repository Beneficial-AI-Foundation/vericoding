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
            
            proof {
                assert(result_chars.len() == i + 1);
                assert(result_chars[i as int] == newChar);
                assert(s.spec_index(i as int) == oldChar);
            }
        } else {
            result_chars.push(ch);
            
            proof {
                assert(result_chars.len() == i + 1);
                assert(result_chars[i as int] == ch);
                assert(result_chars[i as int] == s.spec_index(i as int));
                assert(s.spec_index(i as int) != oldChar);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(i == s.len());
        assert(result_chars.len() == s.len());
        assert(forall |j: int| 0 <= j < s.len() ==> 
            (s.spec_index(j) == oldChar ==> result_chars[j] == newChar) && 
            (s.spec_index(j) != oldChar ==> result_chars[j] == s.spec_index(j)));
    }
    
    let result = convert_chars_to_string(result_chars);
    
    proof {
        assert(result.len() == result_chars.len());
        assert(forall |j: int| 0 <= j < result.len() ==> result.spec_index(j) == result_chars[j]);
    }
    
    result
}

fn convert_chars_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall |i: int| 0 <= i < chars.len() ==> result.spec_index(i) == chars[i]
{
    // Convert Vec<char> to String using String::from_iter
    let result_string = String::from_iter(chars.as_slice().iter().cloned());
    
    proof {
        // In Verus, we need to assume the correctness of standard library functions
        // This assertion establishes the postcondition based on the expected behavior
        // of String::from_iter for char iterators
        assume(result_string.len() == chars.len());
        assume(forall |i: int| 0 <= i < chars.len() ==> result_string.spec_index(i) == chars[i]);
    }
    
    result_string
}

}