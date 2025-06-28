use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) + 32
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn ToLowercase(s: String) -> (v: String)
    requires
        // Ensure string contains only ASCII characters for simplicity
        forall|i: int| 0 <= i < s.len() ==> 0 <= s.spec_index(i) as int <= 127
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsUpperCase(s.spec_index(i)) then 
                IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) 
            else 
                v.spec_index(i) == s.spec_index(i)
{
    let s_bytes = s.as_bytes();
    let mut result_bytes: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    while i < s_bytes.len()
        invariant
            result_bytes.len() == i,
            i <= s_bytes.len(),
            s_bytes.len() == s.len(),
            forall|j: int| 0 <= j < i ==> 0 <= result_bytes[j] as int <= 127,
            forall|j: int| 0 <= j < i ==> {
                let orig_char = s.spec_index(j);
                let result_char = result_bytes[j] as char;
                if IsUpperCase(orig_char) then 
                    IsUpperLowerPair(orig_char, result_char)
                else 
                    result_char == orig_char
            }
    {
        let byte_val = s_bytes[i];
        let c = byte_val as char;
        
        // Since we have the precondition that all chars are ASCII,
        // we know byte_val represents the same character as s.spec_index(i)
        assert(c == s.spec_index(i as int));
        
        if IsUpperCase(c) {
            // Convert to lowercase by adding 32
            let lower_byte = byte_val + 32;
            let lower_c = lower_byte as char;
            result_bytes.push(lower_byte);
            
            // Proof that the conversion is correct
            assert((c as int) == (lower_c as int) - 32);
            assert(IsUpperLowerPair(c, lower_c));
        } else {
            result_bytes.push(byte_val);
            let result_char = byte_val as char;
            assert(result_char == c);
        }
        
        i += 1;
    }
    
    // Convert back to string
    let result = String::from_utf8(result_bytes).unwrap();
    
    // Final assertions to help verification
    assert(result.len() == s.len());
    
    result
}

}