// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            s.len() == i,
            forall|j: int| 0 <= j < i as int ==> s[j] == a[j],
        decreases a.len() - i
    {
        s.push(a[i]);
        i = i + 1;
    }
    s
}
// </vc-code>

}
fn main() {}