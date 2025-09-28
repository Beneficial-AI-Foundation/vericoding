use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn seq_concat_to_multiset_lemma<T>(a: Seq<T>, b: Seq<T>)
    ensures
        (a + b).to_multiset() == a.to_multiset().add(b.to_multiset())
{
    // The multiset of a concatenation equals the sum of multisets
    // This is a fundamental property that Verus understands
    assert((a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()));
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
    let mut c = Vec::new();
    
    // Copy elements from a
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c.len() == i,
            c@ == a@.subrange(0, i as int),
            forall|j: int| 0 <= j < i ==> c[j] == a[j],
    {
        c.push(a[i]);
        i += 1;
    }
    
    assert(c@ == a@);
    
    // Copy elements from b
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            c.len() == a.len() + j,
            c@ == a@ + b@.subrange(0, j as int),
            forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
            forall|k: int| a.len() <= k < c.len() ==> c[k] == b[k - a.len()],
    {
        c.push(b[j]);
        j += 1;
    }
    
    assert(b@.subrange(0, b.len() as int) == b@);
    assert(c@ == a@ + b@);
    
    // Prove multiset equality
    proof {
        seq_concat_to_multiset_lemma(a@, b@);
        assert((a@ + b@).to_multiset() == a@.to_multiset().add(b@.to_multiset()));
        assert(c@.to_multiset() == (a@ + b@).to_multiset());
        assert(c@.to_multiset() == a@.to_multiset().add(b@.to_multiset()));
    }
    
    c
}
// </vc-code>

fn main() {}

}