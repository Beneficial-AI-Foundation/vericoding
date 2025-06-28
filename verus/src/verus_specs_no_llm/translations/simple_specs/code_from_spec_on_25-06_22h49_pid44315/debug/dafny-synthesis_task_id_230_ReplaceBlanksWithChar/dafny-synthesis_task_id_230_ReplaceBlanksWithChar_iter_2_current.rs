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
    let s_seq = s.as_bytes();
    let mut result_vec: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    while i < s_seq.len()
        invariant
            i <= s_seq.len(),
            result_vec.len() == i,
            s_seq.len() == s.len(),
            forall|j: int| 0 <= j < i ==> {
                let s_char = s_seq[j] as char;
                let result_char = result_vec[j] as char;
                (s_char == ' ' ==> result_char == ch) && (s_char != ' ' ==> result_char == s_char)
            }
    {
        let current_byte = s_seq[i];
        let current_char = current_byte as char;
        
        if current_char == ' ' {
            result_vec.push(ch as u8);
        } else {
            result_vec.push(current_byte);
        }
        i += 1;
    }
    
    // Convert back to String
    let result_string = String::from_utf8(result_vec).unwrap();
    
    // Proof that the conversion preserves our properties
    assert(result_string.len() == s.len());
    assert(forall|i: int| 0 <= i < s.len() ==> 
        (s.spec_index(i) == ' ' ==> result_string.spec_index(i) == ch) && 
        (s.spec_index(i) != ' ' ==> result_string.spec_index(i) == s.spec_index(i))
    );
    
    result_string
}

}