use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
// (No helpers needed for this proof.)
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
    let mut v = String::new();
    let mut it = s.chars();
    let len: int = (s@).len() as int;
    let mut i: int = 0;
    while i < len {
        invariant (0 <= i && i <= len);
        invariant (((v@).len() as int) == i);
        invariant (forall |j: int| 0 <= j && j < i ==>
            (if is_space_comma_dot(s@[j]) {
                (v@)@[j] == ':'
            } else {
                (v@)@[j] == s@[j]
            }));
        decreases (len - i);
        match it.next() {
            Some(c) => {
                if is_space_comma_dot(c) {
                    v.push(':');
                } else {
                    v.push(c);
                }
            }
            None => {
                unreached();
            }
        }
        i += 1;
    }
    v
}
// </vc-code>

fn main() {}

}