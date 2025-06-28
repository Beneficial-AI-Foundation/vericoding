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
            let new_code = (c as int) - 32;
            proof {
                assert(97 <= c as int <= 122);
                assert(65 <= new_code <= 90);
                assert(new_code == (c as int) - 32);
            }
            new_code as char
        } else if IsUpperCase(c) {
            // Convert uppercase to lowercase: add 32  
            let new_code = (c as int) + 32;
            proof {
                assert(65 <= c as int <= 90);
                assert(97 <= new_code <= 122);
                assert(new_code == (c as int) + 32);
            }
            new_code as char
        } else {
            // Keep other characters unchanged
            c
        };
        
        proof {
            // Proof assertions to help verification
            if IsLowerCase(c) {
                assert(97 <= c as int <= 122);
                assert((c as int) == (new_char as int) + 32);
                assert(IsLowerUpperPair(c, new_char));
            } else if IsUpperCase(c) {
                assert(65 <= c as int <= 90);
                assert((c as int) == (new_char as int) - 32);
                assert(IsUpperLowerPair(c, new_char));
            } else {
                assert(new_char == c);
            }
        }
        
        result.push(new_char);
        
        proof {
            // Help establish the connection for the next iteration
            assert(result@.index(i as int) == new_char);
            assert(s@.index(i as int) == c);
        }
        
        i += 1;
    }
    
    result
}

}