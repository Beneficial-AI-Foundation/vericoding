use vstd::prelude::*;

verus! {

// <vc-helpers>
trait Subsequence<T> {
    spec fn subsequence_spec(&self, start: int, end: int) -> Seq<T>;
}

impl<T> Subsequence<T> for Seq<T> {
    spec fn subsequence_spec(&self, start: int, end: int) -> Seq<T> {
        self.subsequence(start, end)
    }
}
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
    let mut c: Vec<i32> = Vec::with_capacity(a.len() + b.len());
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            c.len() as int == i as int,
            forall|k: int| 0 <= k < i as int ==> c[k as usize] == a[k as usize],
    {
        c.push(a[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < b.len()
        invariant
            0 <= j as int <= b.len() as int,
            c.len() as int == a.len() as int + j as int,
            forall|k: int| 0 <= k < a.len() as int ==> c[k as usize] == a[k as usize],
            forall|k: int| a.len() as int <= k < a.len() as int + j as int ==> c[k as usize] == b[(k - a.len() as int) as usize],
    {
        c.push(b[j]);
        j = j + 1;
    }

    assert(c.len() == (a.len() + b.len()));
    
    proof {
        // Proof for a@ + b@ == c@
        // Split c@ into two parts: c_prefix (first a.len() elements) and c_suffix (rest of the elements)
        let c_prefix = c@.subsequence_spec(0, a.len() as int);
        let c_suffix = c@.subsequence_spec(a.len() as int, c.len() as int);

        // Prove c_prefix == a@
        assert forall |k: int| 0 <= k < a.len() as int implies #[trigger] c@[k] == a@[k as usize] by {
            // This is maintained by the first loop invariant
        }
        assert(c_prefix == a@);

        // Prove c_suffix == b@
        assert forall |k: int| 0 <= k < b.len() as int implies #[trigger] c@[a.len() as int + k] == b@[k as usize] by {
            // This is maintained by the second loop invariant when k in the second loop is (a.len() + k_relative)
            // (k - a.len()) as usize == k_relative
        }
        assert(c_suffix == b@);

        // Combine
        assert(c_prefix + c_suffix == c@);
        assert(a@ + b@ == c@);
    }
    assert((a@ + b@).to_multiset() == c@.to_multiset()); // auto-verified by Verus if a@ + b@ == c@
    assert(a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset()); // auto-verified by Verus if a@ + b@ == c@

    c
}
// </vc-code>

fn main() {}

}