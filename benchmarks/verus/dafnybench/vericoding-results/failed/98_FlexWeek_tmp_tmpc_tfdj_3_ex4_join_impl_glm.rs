use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_append_multiset<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        (s1 + s2).to_multiset() == s1.to_multiset().add(s2.to_multiset()),
{
    assert(s1.to_multiset().add(s2.to_multiset()) =~= (s1 + s2).to_multiset());
}

proof fn lemma_seq_index_append<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        forall|i: int| 0 <= i < s1.len() ==> (s1 + s2)[i] == s1[i],
        forall|i: int, j: int| 
            s1.len() <= i < (s1 + s2).len() && 
            0 <= j < s2.len() && 
            i - j == s1.len() ==> (s1 + s2)[i] == s2[j],
{
    assert(forall|i: int| 0 <= i < s1.len() ==> (s1 + s2)[i] == s1[i]);
    assert(forall|i: int| s1.len() <= i < (s1 + s2).len() ==> (s1 + s2)[i] == s2[i - s1.len()]);
}

proof fn lemma_vec_seq_append_multiset<T>(v1: Vec<T>, v2: Vec<T>)
    ensures
        (v1@ + v2@).to_multiset() == v1@.to_multiset().add(v2@.to_multiset()),
{
    lemma_seq_append_multiset(v1@, v2@);
}

proof fn lemma_vec_seq_index_append<T>(v1: Vec<T>, v2: Vec<T>)
    ensures
        forall|i: int| 0 <= i < v1.len() ==> (v1@ + v2@)[i] == v1@[i],
        forall|i: int, j: int| 
            v1.len() <= i < (v1@ + v2@).len() && 
            0 <= j < v2.len() && 
            i - j == v1.len() ==> (v1@ + v2@)[i] == v2@[j],
{
    lemma_seq_index_append(v1@, v2@);
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
    let mut c = Vec::with_capacity(a.len() + b.len());
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c.len() == i,
            forall|k: int| 0 <= k < i ==> c[k] == a[k],
            c@.subrange(0, i as int) == a@.subrange(0, i as int),
            c@.to_multiset() == a@.subrange(0, i as int).to_multiset(),
        decreases a.len() - i,
    {
        c.push(a[i]);
        i += 1;
    }
    
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            c.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
            forall|k: int, l: int| 
                a.len() <= k < a.len() + j && 
                0 <= l < j && 
                k - l == a.len() ==> c[k] == b[l],
            c@.subrange(a.len() as int, (a.len() + j) as int) == b@.subrange(0, j as int),
            c@ =~= a@ + b@.subrange(0, j as int),
            c@.to_multiset() == a@.to_multiset().add(b@.subrange(0, j as int).to_multiset()),
        decreases b.len() - j,
    {
        c.push(b[j]);
        j += 1;
    }
    
    assert(c.len() == a.len() + b.len());
    assert(c@ =~= a@ + b@);
    proof {
        lemma_seq_append_multiset(a@, b@);
        lemma_seq_index_append(a@, b@);
    }
    
    c
}
// </vc-code>

fn main() {}

}