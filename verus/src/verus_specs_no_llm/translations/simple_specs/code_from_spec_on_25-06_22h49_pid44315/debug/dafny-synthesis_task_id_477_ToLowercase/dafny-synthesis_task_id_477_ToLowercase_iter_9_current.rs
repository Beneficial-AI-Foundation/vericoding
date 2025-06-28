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
            char::from_u32(lower_val as u32)
        } else {
            first_char
        };
        
        let converted_rest = ToLowercase(rest);
        
        // Proof assertions
        if IsUpperCase(first_char) {
            let upper_val = first_char as int;
            let lower_val = upper_val + 32;
            let lower_char = char::from_u32(lower_val as u32);
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
            let orig_char = char::from_u32(s[i] as u32);
            let result_char = char::from_u32(v[i] as u32);
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
                let orig_char = char::from_u32(s[j] as u32);
                let result_char = char::from_u32(result[j] as u32);
                if IsUpperCase(orig_char) then 
                    IsUpperLowerPair(orig_char, result_char)
                else 
                    result_char == orig_char
            }
    {
        let byte_val = s[i];
        let c = char::from_u32(byte_val as u32);
        
        if IsUpperCase(c) {
            // Convert to lowercase by adding 32
            let lower_byte = byte_val + 32;
            let lower_c = char::from_u32(lower_byte as u32);
            
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
            let result_char = char::from_u32(byte_val as u32);
            assert(result_char == c);
            result.push(byte_val);
        }
        
        i += 1;
    }
    
    result
}

}