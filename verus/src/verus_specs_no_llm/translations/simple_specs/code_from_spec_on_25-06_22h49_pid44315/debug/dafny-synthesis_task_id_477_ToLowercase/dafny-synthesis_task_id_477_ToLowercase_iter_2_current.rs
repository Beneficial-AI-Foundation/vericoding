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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            result.len() == i,
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> 
                if IsUpperCase(s.spec_index(j)) then 
                    IsUpperLowerPair(s.spec_index(j), result.spec_index(j))
                else 
                    result.spec_index(j) == s.spec_index(j)
    {
        // Get character at position i
        let c = s.as_bytes()[i] as char;
        
        if IsUpperCase(c) {
            // Convert to lowercase by adding 32
            let lower_c_code = (c as u32) + 32;
            assert(lower_c_code <= 127); // Ensure it's valid ASCII
            let lower_c = char::from_u32(lower_c_code).unwrap();
            result.push(lower_c);
            
            // Proof that the conversion is correct
            assert(IsUpperLowerPair(c, lower_c));
        } else {
            result.push(c);
        }
        
        i += 1;
    }
    
    // Convert Vec<char> back to String
    let result_string = String::from_iter(result.iter());
    
    // Proof that lengths match
    assert(result_string.len() == s.len());
    
    // Proof that character conversions are correct
    assert(forall|j: int| 0 <= j < s.len() ==> 
        if IsUpperCase(s.spec_index(j)) then 
            IsUpperLowerPair(s.spec_index(j), result_string.spec_index(j))
        else 
            result_string.spec_index(j) == s.spec_index(j));
    
    result_string
}

}