use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
spec fn char_at(s: Seq<char>, i: int) -> char
    recommends 0 <= i < s.len()
{
    s[i]
}
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
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.unicode_len()
        invariant
            i <= s.unicode_len(),
            v.len() == i,
            v@.len() == i as int,
            forall|j: int| 0 <= j < i ==> {
                if is_space_comma_dot(s@[j]) {
                    v@[j] == ':'
                } else {
                    v@[j] == s@[j]
                }
            }
    {
        let c = s.get_char(i);
        if c == ' ' || c == ',' || c == '.' {
            v.push(':');
        } else {
            v.push(c);
        }
        i = i + 1;
    }
    
    let result = String::from_iter(v.iter());
    result
}
// </vc-code>

fn main() {}

}