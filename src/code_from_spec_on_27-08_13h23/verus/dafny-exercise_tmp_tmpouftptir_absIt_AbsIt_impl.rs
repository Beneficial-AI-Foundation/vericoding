use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// </vc-spec>

// <vc-code>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i ==> 
                if old(s)[j] < 0 { s[j] == -old(s)[j] } else { s[j] == old(s)[j] },
            forall|j: int| i <= j < s.len() ==> s[j] == old(s)[j]
    {
        if s[i] < 0 {
            s.set(i, -s[i]);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}