use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
proof fn string_push_char_properties(s: String, c: char)
    ensures 
        s@.len() + 1 == (s@ + seq![c]).len(),
        forall|i: int| 0 <= i < s@.len() ==> (s@ + seq![c])[i] == s@[i],
        (s@ + seq![c])[s@.len() as int] == c
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = String::new_strlit("");
    let mut i = 0;
    
    while i < s.unicode_len()
        invariant
            0 <= i <= s.unicode_len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if is_space_comma_dot(s@[j]) {
                    result@[j] == ':'
                } else {
                    result@[j] == s@[j]
                }
            }
    {
        let c = s.get_char(i);
        let new_char = if is_space_comma_dot(c) { ':' } else { c };
        
        proof {
            string_push_char_properties(result, new_char);
        }
        
        result.push(new_char);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}