use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == a[j],
    {
        v.push(a[i]);
        i = i + 1;
    }
    
    v
}
// </vc-code>

fn main() {
}

}