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
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i ==> 
                if old(s)[j] < 0 { s[j] == -old(s)[j] } else { s[j] == old(s)[j] },
            forall|j: int| i <= j < s.len() ==> s[j] == old(s)[j]
        decreases s.len() - i
    {
        let val = s[i];
        if val < 0 {
            proof {
                assert(val >= i32::MIN);
                assert(val != i32::MIN);
                assert(-val > 0);
                assert(-val <= i32::MAX);
            }
            s.set(i, -val);
        }
        i += 1;
        proof {
            assert(i <= s.len());
        }
    }
}
// </vc-code>

fn main() {}

}