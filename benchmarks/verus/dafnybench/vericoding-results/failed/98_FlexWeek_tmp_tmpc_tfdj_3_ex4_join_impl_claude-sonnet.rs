use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_seq_concat_to_multiset<T>(a: Seq<T>, b: Seq<T>)
    ensures (a + b).to_multiset() == a.to_multiset().add(b.to_multiset())
{
    let ab = a + b;
    assert(ab.len() == a.len() + b.len());
    
    assert forall |x: T| ab.to_multiset().count(x) == a.to_multiset().count(x) + b.to_multiset().count(x) by {
        assert(ab.to_multiset().count(x) == 
               a.to_multiset().count(x) + b.to_multiset().count(x));
    };
    
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
    
    for i in 0..a.len()
        invariant
            c.len() == i,
            c@ == a@.subrange(0, i as int),
    {
        c.push(a[i]);
    }
    
    for i in 0..b.len()
        invariant
            c.len() == a.len() + i,
            c@ == a@ + b@.subrange(0, i as int),
    {
        c.push(b[i]);
    }
    
    proof {
        assert(c@ == a@ + b@);
        assert(c.len() == a.len() + b.len());
        
        // Prove the first forall condition
        assert forall|i: int| 0 <= i < a.len() implies c[i] == a[i] by {
            assert(c@[i] == (a@ + b@)[i]);
            assert((a@ + b@)[i] == a@[i]);
        };
        
        // Prove the second forall condition  
        assert forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() implies c[i] == b[j] by {
            assert(i == a.len() + j);
            assert(c@[i] == (a@ + b@)[i]);
            assert((a@ + b@)[i] == b@[j]);
        };
        
        // Prove multiset properties using the lemma
        lemma_seq_concat_to_multiset(a@, b@);
        assert((a@ + b@).to_multiset() == a@.to_multiset().add(b@.to_multiset()));
    }
    
    c
}
// </vc-code>

fn main() {}

}