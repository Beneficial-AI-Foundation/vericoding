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
            if IsLowerCase(s.spec_index(i)) then 
                IsLowerUpperPair(s.spec_index(i), v.spec_index(i)) 
            else if IsUpperCase(s.spec_index(i)) then 
                IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) 
            else 
                v.spec_index(i) == s.spec_index(i)
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if IsLowerCase(s.spec_index(j)) then 
                    IsLowerUpperPair(s.spec_index(j), result.spec_index(j)) 
                else if IsUpperCase(s.spec_index(j)) then 
                    IsUpperLowerPair(s.spec_index(j), result.spec_index(j)) 
                else 
                    result.spec_index(j) == s.spec_index(j)
    {
        let c = s[i];
        let new_char = if IsLowerCase(c) {
            // Convert lowercase to uppercase: subtract 32
            char::from_u32_unchecked((c as u32) - 32)
        } else if IsUpperCase(c) {
            // Convert uppercase to lowercase: add 32  
            char::from_u32_unchecked((c as u32) + 32)
        } else {
            // Keep other characters unchanged
            c
        };
        
        // Proof assertions to help verification
        assert(IsLowerCase(c) ==> IsLowerUpperPair(c, new_char));
        assert(IsUpperCase(c) ==> IsUpperLowerPair(c, new_char));
        assert(!IsLowerCase(c) && !IsUpperCase(c) ==> new_char == c);
        
        result.push(new_char);
        i += 1;
    }
    
    result
}

}