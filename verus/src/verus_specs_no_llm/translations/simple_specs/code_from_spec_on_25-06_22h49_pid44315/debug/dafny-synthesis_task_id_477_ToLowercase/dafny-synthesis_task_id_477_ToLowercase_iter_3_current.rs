use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

fn ToLowercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsUpperCase(s.spec_index(i)) then 
                IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) 
            else 
                v.spec_index(i) == s.spec_index(i)
{
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let s_bytes = s.as_bytes();
    
    while i < s.len()
        invariant
            result.len() == i,
            i <= s.len(),
            s_bytes.len() == s.len(),
            forall|j: int| 0 <= j < i ==> 
                if IsUpperCase(s.spec_index(j)) then 
                    IsUpperLowerPair(s.spec_index(j), result.spec_index(j) as char)
                else 
                    result.spec_index(j) as char == s.spec_index(j)
    {
        // Get byte at position i
        let c_byte = s_bytes[i];
        let c = c_byte as char;
        
        if IsUpperCase(c) {
            // Convert to lowercase by adding 32
            let lower_c_byte = c_byte + 32;
            result.push(lower_c_byte);
            
            // Proof that the conversion is correct
            assert(IsUpperLowerPair(c, lower_c_byte as char));
        } else {
            result.push(c_byte);
        }
        
        i += 1;
    }
    
    // Convert Vec<u8> back to String
    let result_string = String::from_utf8(result).unwrap();
    
    // Proof that lengths match
    assert(result_string.len() == s.len());
    
    result_string
}

}