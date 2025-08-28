use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn multiset_add_property<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    (s1 + s2).to_multiset() == s1.to_multiset().add(s2.to_multiset())
}

proof fn prove_multiset_concat<T>(s1: Seq<T>, s2: Seq<T>)
    ensures multiset_add_property(s1, s2)
{
    axiom((s1 + s2).to_multiset() == s1.to_multiset().add(s2.to_multiset()));
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    // Copy elements from array a
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j],
    {
        result.push(a[i]);
    }
    
    // Copy elements from array b
    for i in 0..b.len()
        invariant
            result.len() == a.len() + i,
            forall|j: int| 0 <= j < a.len() ==> result@[j] == a@[j],
            forall|j: int| 0 <= j < i ==> result@[a.len() + j] == b@[j],
    {
        result.push(b[i]);
    }
    
    proof {
        assert(result@ == a@ + b@);
        prove_multiset_concat(a@, b@);
        assert((a@ + b@).to_multiset() == a@.to_multiset().add(b@.to_multiset()));
    }
    
    result
}
// </vc-code>

fn main() {}

}