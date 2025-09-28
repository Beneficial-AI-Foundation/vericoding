use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len();
        invariant c.len() == (i as nat);
        invariant c@ == a@[..i];
        decreases a.len() - i;
    {
        c.push(a@[i]);
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        assert(a@[..i].len() == i);
        assert(a@.len() == a.len());
        assert(a@[..i].len() == a@.len());
        assert(forall|k: int| 0 <= k < a@.len() ==> a@[..i]@[k] == a@[k]);
        assert(a@[..i] == a@);
        assert(c@ == a@);
    }

    let mut j: int = 0;
    while j < b.len()
        invariant 0 <= j && j <= b.len();
        invariant c.len() == ((a.len() + j) as nat);
        invariant c@ == a@ + b@[..j];
        decreases b.len() - j;
    {
        c.push(b@[j]);
        j = j + 1;
    }
    proof {
        assert(j == b.len());
        assert(b@[..j].len() == j);
        assert(b@.len() == b.len());
        assert(b@[..j].len() == b@.len());
        assert(forall|k: int| 0 <= k < b@.len() ==> b@[..j]@[k] == b@[k]);
        assert(b@[..j] == b@);
        assert(c@ == a@ + b@);
    }

    c
}
// </vc-code>

fn main() {}

}