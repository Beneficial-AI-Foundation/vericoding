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
        let current_char = s_seq.index(i as int);
        
        if current_char == ' ' {
            result.push(ch);
        } else {
            result.push(current_char);
        }
        
        proof {
            assert(current_char == s_seq.index(i as int));
            assert(result.len() == i + 1);
            
            if current_char == ' ' {
                assert(result@.index(i as int) == ch);
                assert(s_seq.index(i as int) == ' ' ==> result@.index(i as int) == ch);
            } else {
                assert(result@.index(i as int) == current_char);
                assert(result@.index(i as int) == s_seq.index(i as int));
                assert(s_seq.index(i as int) != ' ' ==> result@.index(i as int) == s_seq.index(i as int));
            }
            
            // Maintain invariant for all previous positions
            assert(forall|j: int| 0 <= j < i ==> {
                (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
                (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
            }) by {
                // This follows from the loop invariant
            };
            
            // Show the invariant holds for the new position
            assert({
                (s_seq.index(i as int) == ' ' ==> result@.index(i as int) == ch) && 
                (s_seq.index(i as int) != ' ' ==> result@.index(i as int) == s_seq.index(i as int))
            });
            
            // Combine to show invariant for range [0, i+1)
            assert(forall|j: int| 0 <= j < i + 1 ==> {
                (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
                (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
            }) by {
                assert(forall|j: int| 0 <= j < i ==> {
                    (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
                    (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
                });
                assert({
                    (s_seq.index(i as int) == ' ' ==> result@.index(i as int) == ch) && 
                    (s_seq.index(i as int) != ' ' ==> result@.index(i as int) == s_seq.index(i as int))
                });
            };
        }
        
        i += 1;
    }
    
    proof {
        assert(i == s.len());
        assert(result.len() == s.len());
        assert(s_seq == s@);
        assert(forall|j: int| 0 <= j < s.len() ==> {
            (s_seq.index(j) == ' ' ==> result@.index(j) == ch) && 
            (s_seq.index(j) != ' ' ==> result@.index(j) == s_seq.index(j))
        });
        assert(forall|j: int| 0 <= j < s.len() ==> {
            (s@.index(j) == ' ' ==> result@.index(j) == ch) && 
            (s@.index(j) != ' ' ==> result@.index(j) == s@.index(j))
        }) by {
            assert(s_seq == s@);
        };
    }
    
    result
}

}