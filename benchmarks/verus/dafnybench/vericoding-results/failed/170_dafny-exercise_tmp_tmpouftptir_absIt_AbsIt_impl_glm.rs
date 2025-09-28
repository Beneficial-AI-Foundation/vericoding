use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n = s.len();
    while i < n
        invariant
            0 <= i <= n,
            s.len() == n,
            forall|k: int| 0 <= k < i ==> 
                if old(s)[k] < 0 { s[k] == -old(s)[k] } else { s[k] == old(s)[k] },
            forall|k: int| i <= k < n ==> s[k] == old(s)[k]
    {
        let val = s[i];
        if val < 0 {
            s.set(i, -val);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}