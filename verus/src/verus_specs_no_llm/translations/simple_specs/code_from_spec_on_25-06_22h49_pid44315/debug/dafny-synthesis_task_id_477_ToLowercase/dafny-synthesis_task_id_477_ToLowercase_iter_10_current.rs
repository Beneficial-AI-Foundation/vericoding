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

spec fn char_from_u8(b: u8) -> char {
    b as char
}

fn ToLowercase(s: Seq<char>) -> (v: Seq<char>)
    requires
        // Ensure string contains only ASCII characters for simplicity
        forall|i: int| 0 <= i < s.len() ==> 0 <= s[i] as int <= 127
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsUpperCase(s[i]) then 
                IsUpperLowerPair(s[i], v[i]) 
            else 
                v[i] == s[i]
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let first_char = s[0];
        let rest = s.subrange(1, s.len() as int);
        
        let converted_first = if IsUpperCase(first_char) {
            // Convert uppercase to lowercase by adding 32 to the ASCII value
            let upper_val = first_char as int;
            let lower_val = upper_val + 32;
            // Prove the conversion is valid
            assert(65 <= upper_val <= 90);
            assert(97 <= lower_val <= 122);
            assert(lower_val <= 127);
            (lower_val as u8) as char
        } else {
            first_char
        };
        
        let converted_rest = ToLowercase(rest);
        
        // Proof assertions
        if IsUpperCase(first_char) {
            let upper_val = first_char as int;
            let lower_val = upper_val + 32;
            let lower_char = (lower_val as u8) as char;
            assert((first_char as int) == (lower_char as int) - 32);
            assert(IsUpperLowerPair(first_char, lower_char));
            assert(converted_first == lower_char);
        }
        
        seq![converted_first].add(converted_rest)
    }
}

// Helper function using Vec for practical implementation
fn ToLowercaseVec(s: Vec<u8>) -> (v: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> 0 <= s[i] as int <= 127,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0  // u8 is always >= 0, but needed for proof
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            let orig_char = s[i] as char;
            let result_char = v[i] as char;
            if IsUpperCase(orig_char) then 
                IsUpperLowerPair(orig_char, result_char)
            else 
                result_char == orig_char
        }
{
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            result.len() == i,
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> 0 <= s[j] as int <= 127,
            forall|j: int| 0 <= j < i ==> 0 <= result[j] as int <= 127,
            forall|j: int| 0 <= j < i ==> {
                let orig_char = s[j] as char;
                let result_char = result[j] as char;
                if IsUpperCase(orig_char) then 
                    IsUpperLowerPair(orig_char, result_char)
                else 
                    result_char == orig_char
            }
    {
        let byte_val = s[i];
        let c = byte_val as char;
        
        if IsUpperCase(c) && byte_val <= 95 {  // Additional safety check
            // Convert to lowercase by adding 32
            let lower_byte = byte_val + 32;
            let lower_c = lower_byte as char;
            
            // Proof assertions
            assert(65 <= byte_val <= 90);  // byte_val is uppercase ASCII
            assert(97 <= lower_byte <= 122);  // lower_byte is lowercase ASCII
            assert(lower_byte <= 127);  // still ASCII
            assert((c as int) == (byte_val as int));
            assert((lower_c as int) == (lower_byte as int));
            assert((c as int) == (lower_c as int) - 32);
            assert(IsUpperLowerPair(c, lower_c));
            
            result.push(lower_byte);
        } else {
            let result_char = byte_val as char;
            assert(result_char == c);
            result.push(byte_val);
        }
        
        i += 1;
    }
    
    result
}

}