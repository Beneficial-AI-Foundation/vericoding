use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_string_into_chars(s: Vec<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[i] == s[i],
// </vc-spec>
// <vc-code>
{
    let mut v = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == s[j],
        decreases
            s.len() - i,
    {
        v.push(s[i]);
        i += 1;
    }
    
    v
}
// </vc-code>

fn main() {
}

}