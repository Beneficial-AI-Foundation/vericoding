use vstd::prelude::*;

verus! {

// <vc-helpers>
fn array_to_seq(a: &Vec<i32>) -> (s: Seq<i32>)
    ensures
        s.len() == a.len() as nat,
        forall|i: int| 0 <= i && (i as usize) < a.len() ==> s[i] == a[i as usize],
{
    let mut s: Seq<i32> = Seq::empty();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            s.len() == i as nat,
            forall|j: int| 0 <= j && (j as usize) < i ==> s[j] == a[j as usize],
    {
        s = s.push(a[i]);
        i = i + 1;
    }
    s
}
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
    let a_seq = array_to_seq(a); // This line is for verification assistance, array_to_seq ensures a_seq accurately represents 'a'.
    let mut r = s;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            r.len() == s.len() + i as nat,
            forall|j: int| 0 <= j < s.len() ==> r[j] == s[j],
            forall|j: int| 0 <= j && (j as usize) < i ==> #[trigger] r[s.len() + j] == a[j as usize],
    {
        r = r.push(a[i]);
        i = i + 1;
    }
    r
}
// </vc-code>

fn main() {}

}