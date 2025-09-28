use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let orig = ghost(s@);
    let n = s.len();
    for i in 0..n
        invariant 
            s.len() == n,
            forall|j: int| 0 <= j < i as int ==> s@[j] == 2 * orig@[j]
    {
        assert(s[i] >= i32::MIN / 2 && s[i] <= i32::MAX / 2);
        s[i] = 2 * s[i];
    }
}
// </vc-code>

fn main() {
}

}