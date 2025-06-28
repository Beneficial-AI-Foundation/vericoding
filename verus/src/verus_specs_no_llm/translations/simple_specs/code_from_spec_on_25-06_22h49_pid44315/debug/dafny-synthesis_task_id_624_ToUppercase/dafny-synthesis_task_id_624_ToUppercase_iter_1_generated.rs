use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

fn ToUppercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> if IsLowerCase(s.spec_index(i)) then IsLowerUpperPair(s.spec_index(i), v.spec_index(i)) else v.spec_index(i) == s.spec_index(i)
{
    let mut result = String::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall j :: 0 <= j < i ==> if IsLowerCase(s.spec_index(j)) then IsLowerUpperPair(s.spec_index(j), result.spec_index(j)) else result.spec_index(j) == s.spec_index(j)
    {
        let c = s.spec_index(i);
        let new_char = if IsLowerCase(c) {
            // Convert to uppercase: subtract 32 from ASCII value
            char::from_u32((c as u32) - 32).unwrap()
        } else {
            c
        };
        
        // Prove the property for the character we're about to add
        assert(if IsLowerCase(c) then IsLowerUpperPair(c, new_char) else new_char == c);
        
        result.push(new_char);
        i += 1;
    }
    
    result
}

}