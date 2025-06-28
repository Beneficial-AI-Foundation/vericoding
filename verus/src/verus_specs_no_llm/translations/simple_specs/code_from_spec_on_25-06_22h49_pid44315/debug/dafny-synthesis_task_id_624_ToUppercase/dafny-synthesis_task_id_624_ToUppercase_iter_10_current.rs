use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn char_to_upper(c: char) -> char {
    if IsLowerCase(c) {
        char::from_u32_unchecked((c as u32) - 32)
    } else {
        c
    }
}

fn ToUppercase(s: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    let mut result: Seq<char> = seq![];
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], result[j]) else result[j] == s[j]
    {
        let c = s[i];
        let new_char = if IsLowerCase(c) {
            proof {
                assert(97 <= c as int <= 122);
                assert(65 <= (c as int - 32) <= 90);
                assert((c as u32) >= 97);
                assert((c as u32) >= 32);
                assert((c as u32) - 32 >= 65);
                assert((c as u32) - 32 <= 90);
            }
            char::from_u32_unchecked((c as u32) - 32)
        } else {
            c
        };
        
        proof {
            if IsLowerCase(c) {
                assert((c as u32) >= 97u32);
                assert((c as u32) - 32 >= 65u32);
                assert((c as u32) - 32 <= 90u32);
                assert((new_char as int) == (c as int) - 32);
                assert(IsLowerUpperPair(c, new_char));
            } else {
                assert(new_char == c);
            }
        }
        
        result = result.push(new_char);
        i += 1;
    }
    
    proof {
        assert(i == s.len());
        assert(result.len() == s.len());
        assert(forall|j: int| 0 <= j < s.len() ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], result[j]) else result[j] == s[j]);
    }
    
    result
}

}