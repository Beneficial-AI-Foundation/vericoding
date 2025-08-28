use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s@[i] == 2 * old(s)@[i]
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i as int ==> s@[j] == 2 * old(s)@[j],
            forall|j: int| i as int <= j < s.len() as int ==> s@[j] == old(s)@[j]
    {
        s.set(i, 2 * s@[i]);
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}