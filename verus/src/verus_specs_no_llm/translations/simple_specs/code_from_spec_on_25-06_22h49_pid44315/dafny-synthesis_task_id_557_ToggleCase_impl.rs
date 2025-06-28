use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}

spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

fn ToggleCase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if IsLowerCase(s@.index(i)) then 
                IsLowerUpperPair(s@.index(i), v@.index(i)) 
            else if IsUpperCase(s@.index(i)) then 
                IsUpperLowerPair(s@.index(i), v@.index(i)) 
            else 
                v@.index(i) == s@.index(i)
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if IsLowerCase(s@.index(j)) then 
                    IsLowerUpperPair(s@.index(j), result@.index(j)) 
                else if IsUpperCase(s@.index(j)) then 
                    IsUpperLowerPair(s@.index(j), result@.index(j)) 
                else 
                    result@.index(j) == s@.index(j)
    {
        let c = s@.index(i as int);
        
        let new_char = if IsLowerCase(c) {
            // Convert lowercase to uppercase: subtract 32
            let new_code = (c as u32) - 32;
            proof {
                assert(97 <= c as int <= 122);
                assert(65 <= new_code as int <= 90);
                assert(IsUpperCase(new_code as char));
                assert((c as int) == (new_code as int) + 32);
                assert(IsLowerUpperPair(c, new_code as char));
            }
            char::from_u32(new_code).unwrap()
        } else if IsUpperCase(c) {
            // Convert uppercase to lowercase: add 32  
            let new_code = (c as u32) + 32;
            proof {
                assert(65 <= c as int <= 90);
                assert(97 <= new_code as int <= 122);
                assert(IsLowerCase(new_code as char));
                assert((c as int) == (new_code as int) - 32);
                assert(IsUpperLowerPair(c, new_code as char));
            }
            char::from_u32(new_code).unwrap()
        } else {
            // Keep other characters unchanged
            c
        };
        
        result.push(new_char);
        
        proof {
            assert(result.len() == i + 1);
            assert(result@.index(i as int) == new_char);
            
            // Verify the postcondition for the current character
            if IsLowerCase(c) {
                assert(IsLowerUpperPair(c, new_char));
            } else if IsUpperCase(c) {
                assert(IsUpperLowerPair(c, new_char));
            } else {
                assert(new_char == c);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(forall|k: int| 0 <= k < s.len() ==> 
            if IsLowerCase(s@.index(k)) then 
                IsLowerUpperPair(s@.index(k), result@.index(k)) 
            else if IsUpperCase(s@.index(k)) then 
                IsUpperLowerPair(s@.index(k), result@.index(k)) 
            else 
                result@.index(k) == s@.index(k));
    }
    
    result
}

}