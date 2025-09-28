use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_even(s: &mut Vec<nat>)
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if old(s)[i] % 2 == 1 {
                s[i] == old(s)[i] + 1
            } else {
                s[i] == old(s)[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i ==> {
                if old(s)[j] % 2 == 1 {
                    s[j] == old(s)[j] + 1
                } else {
                    s[j] == old(s)[j]
                }
            },
            forall|j: int| i <= j < s.len() ==> s[j] == old(s)[j]
    {
        if s[i] % 2 == 1 {
            s.set(i, s[i] + 1);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}