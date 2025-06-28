use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (s.spec_index(i) == ' ' ==> v.spec_index(i) == ch) && (s.spec_index(i) != ' ' ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (s.spec_index(j) == ' ' ==> result.spec_index(j) == ch) && 
                (s.spec_index(j) != ' ' ==> result.spec_index(j) == s.spec_index(j))
            }
    {
        let current_char = s.spec_index(i as int);
        
        if current_char == ' ' {
            result.push(ch);
        } else {
            result.push(current_char);
        }
        
        proof {
            assert(result.len() == i + 1);
            assert(forall|j: int| 0 <= j < i ==> {
                (s.spec_index(j) == ' ' ==> result.spec_index(j) == ch) && 
                (s.spec_index(j) != ' ' ==> result.spec_index(j) == s.spec_index(j))
            });
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(forall|i: int| 0 <= i < s.len() ==> 
            (s.spec_index(i) == ' ' ==> result.spec_index(i) == ch) && 
            (s.spec_index(i) != ' ' ==> result.spec_index(i) == s.spec_index(i))
        );
    }
    
    result
}

}