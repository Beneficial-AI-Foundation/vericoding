use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn join(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures
        a@ + b@ == c@,
        (a@ + b@).to_multiset() == c@.to_multiset(),
        a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset(),
        a.len() + b.len() == c.len(),
        // Forall
        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::new();

    let alen = a.len();
    for i in 0..alen
        invariant
            0 <= (i as int) <= (alen as int),
            c@ == a@.subrange(0, i as int),
    {
        c.push(a[i]);
        assert(a@.subrange(0, (i as int) + 1) == a@.subrange(0, i as int) + seq![a@[(i as int)]]);
    }
    assert(c@ == a@);

    let blen = b.len();
    for j in 0..blen
        invariant
            0 <= (j as int) <= (blen as int),
            c@ == a@ + b@.subrange(0, j as int),
    {
        c.push(b[j]);
        assert(b@.subrange(0, (j as int) + 1) == b@.subrange(0, j as int) + seq![b@[(j as int)]]);
    }
    assert(c@ == a@ + b@);

    c
}
// </vc-code>

fn main() {}

}