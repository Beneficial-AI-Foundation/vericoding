use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_i32_negatable(x: i32) -> bool {
    x != i32::MIN
}
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
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i ==> 
                if old(s)[j] < 0 { s[j] == -old(s)[j] } else { s[j] == old(s)[j] },
            forall|j: int| i <= j < s.len() ==> s[j] == old(s)[j],
            forall|j: int| 0 <= j < s.len() ==> is_i32_negatable(old(s)[j])
        decreases s.len() - i
    {
        if s[i] < 0 {
            let val = s[i];
            s.set(i, -val);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}