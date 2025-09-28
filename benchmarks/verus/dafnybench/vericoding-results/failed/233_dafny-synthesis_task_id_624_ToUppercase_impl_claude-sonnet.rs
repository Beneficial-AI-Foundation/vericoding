use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

spec fn shift_minus_32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

// <vc-helpers>
spec fn to_uppercase_char(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32(c)
    } else {
        c
    }
}

proof fn shift_minus_32_creates_pair(c: char)
    requires is_lower_case(c)
    ensures is_lower_upper_pair(c, shift_minus_32(c))
{
    assert(97 <= c as int <= 122);
    assert(shift_minus_32(c) == ((c as int - 32) % 128) as char);
    assert(c as int - 32 >= 65 && c as int - 32 <= 90);
    assert((c as int - 32) % 128 == c as int - 32);
    assert(shift_minus_32(c) == (c as int - 32) as char);
    assert(c as int == (shift_minus_32(c) as int) + 32);
    assert(is_lower_upper_pair(c, shift_minus_32(c)));
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(s: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], v[i])
            } else {
                v[i] == s[i]
            }
// </vc-spec>
// <vc-code>
{
    let result = s.map(|c| to_uppercase_char(c));
    
    proof {
        assert(result.len() == s.len());
        
        assert forall|i: int| 0 <= i < s.len() implies
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], result[i])
            } else {
                result[i] == s[i]
            }
        by {
            if 0 <= i < s.len() {
                assert(result[i] == to_uppercase_char(s[i]));
                if is_lower_case(s[i]) {
                    assert(to_uppercase_char(s[i]) == shift_minus_32(s[i]));
                    shift_minus_32_creates_pair(s[i]);
                    assert(is_lower_upper_pair(s[i], result[i]));
                } else {
                    assert(to_uppercase_char(s[i]) == s[i]);
                    assert(result[i] == s[i]);
                }
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}