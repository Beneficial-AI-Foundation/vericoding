use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (s@.index(i) == ' ' ==> v@.index(i) == ch) && (s@.index(i) != ' ' ==> v@.index(i) == s@.index(i))
{
    let mut result = String::new();
    let mut i: usize = 0;
    let ghost s_seq = s@;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            s_seq == s@,
            forall|j: int| 0 <= j < i ==> {
                (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
                (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
            }
    {
        let s_chars = s.as_bytes();
        let current_char = s_chars[i] as char;
        
        proof {
            assert(current_char == s@.index(i as int));
        }
        
        if current_char == ' ' {
            result.push(ch);
        } else {
            result.push(current_char);
        }
        
        proof {
            assert(result.len() == i + 1);
            let old_result_len = i;
            assert(current_char == s_seq.index(i as int));
            if current_char == ' ' {
                assert(result@.index(i as int) == ch);
            } else {
                assert(result@.index(i as int) == current_char);
                assert(result@.index(i as int) == s_seq.index(i as int));
            }
            
            // Maintain the invariant for all previous indices
            assert(forall|j: int| 0 <= j < i ==> {
                (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
                (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
            });
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(s_seq == s@);
        assert(forall|i: int| 0 <= i < s.len() ==> 
            (s@.index(i) == ' ' ==> result@.index(i) == ch) && 
            (s@.index(i) != ' ' ==> result@.index(i) == s@.index(i))
        );
    }
    
    result
}

}