use vstd::prelude::*;

verus! {

// <vc-helpers>
fn array_to_seq_helper(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
{
    let mut s: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    // #[verifier::loop_invariant_param(a)] // This attribute is not recognized by Verus
    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            s.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] s[j] == a[j],
        decreases a.len() - i,
    {
        s.push(a[i]);
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    array_to_seq_helper(a)
}
// </vc-code>

fn main() {
}

}