use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut s = Vec::new();
    for i in 0..a.len()
        invariant
            0 <= i <= a.len(),
            s.len() == i,
            forall|j: int| 0 <= j < i ==> s@[j] == a[j],
    {
        s.push(a[i]);
    }
    s
}
// </vc-code>

fn main() {
}

}