use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>

// </vc-helpers>

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
// <vc-code>
{
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if is_space_comma_dot(s@[j]) {
                    result@[j] == ':'
                } else {
                    result@[j] == s@[j]
                }
            }
    {
        let c = s@[i as nat];
        
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}