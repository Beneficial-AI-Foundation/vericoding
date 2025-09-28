use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let n = s.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            s@.len() == n,
            n == old(s)@.len(),
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> 
                if old(s)@[j] < 0 { s@[j] == -old(s)@[j] } else { s@[j] == old(s)@[j] },
            forall|j: int| i <= j < n ==> s@[j] == old(s)@[j],
        decreases n - i,
    {
        let val = s[i];
        if val < 0 {
            s.set(i, -val);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}