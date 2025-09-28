use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
// No additional helpers needed; the implementation uses built-in types and the given spec function.
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
    let mut result: String = String::new();
    let mut i: usize = 0;
    let len = s@.len() as usize;
    while i < len
        invariant
            result@.len() == i as nat,
            0 <= i <= len,
            forall|j: int| 0 <= j < i as int ==> if is_space_comma_dot(s@[j]) { result@[j] == ':' } else { result@[j] == s@[j] }
    {
        let ghost c_gh = s@[i as int];
        let c = s.chars().nth(i).unwrap();
        proof { assert(c_gh == c); }
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        i += 1;
        assert(result@.len() == i as nat);
        assert(forall|j: int| 0 <= j < i as int ==> if is_space_comma_dot(s@[j]) { result@[j] == ':' } else { result@[j] == s@[j] });
    }
    assert(result@.len() == s@.len());
    assert(forall|i: int| 0 <= i < s@.len() ==> if is_space_comma_dot(s@[i]) { result@[i] == ':' } else { result@[i] == s@[i] });
    result
}
// </vc-code>

fn main() {}

}