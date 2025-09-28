use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn append_array_to_seq(s: Seq<i32>, a: &Vec<i32>) -> (r: Seq<i32>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
        forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut r = s;
    let alen: int = a.len() as int;
    let mut i: int = 0;
    while i < alen
        invariant 0 <= i && i <= alen;
        invariant r.len() == s.len() + i;
        invariant forall |j: int| 0 <= j && j < s.len() ==> r[j] == s[j];
        invariant forall |j: int| 0 <= j && j < i ==> r[s.len() + j] == a@[j];
        decreases alen - i;
    {
        let x: i32 = a[i as usize];
        r = r.push(x);
        i += 1;
    }
    r
}
// </vc-code>

fn main() {}

}