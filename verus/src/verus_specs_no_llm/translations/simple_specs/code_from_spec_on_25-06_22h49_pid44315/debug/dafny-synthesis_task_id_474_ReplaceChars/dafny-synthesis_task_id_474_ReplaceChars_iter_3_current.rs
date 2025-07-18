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
    let chars: Vec<char> = s.chars().collect();
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= s.len(),
            chars.len() == s.len(),
            result.len() == i,
            forall |j: int| 0 <= j < chars.len() ==> chars[j] == s.spec_index(j),
            forall |j: int| 0 <= j < i ==> (s.spec_index(j) == oldChar ==> result.spec_index(j) == newChar) && (s.spec_index(j) != oldChar ==> result.spec_index(j) == s.spec_index(j))
    {
        let ch = chars[i];
        
        proof {
            assert(ch == s.spec_index(i as int));
        }
        
        if ch == oldChar {
            result.push(newChar);
            
            proof {
                assert(result.len() == i + 1);
                assert(result.spec_index(i as int) == newChar);
                assert(s.spec_index(i as int) == oldChar);
            }
        } else {
            result.push(ch);
            
            proof {
                assert(result.len() == i + 1);
                assert(result.spec_index(i as int) == ch);
                assert(result.spec_index(i as int) == s.spec_index(i as int));
                assert(s.spec_index(i as int) != oldChar);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(i == s.len());
        assert(result.len() == s.len());
    }
    
    result
}

}