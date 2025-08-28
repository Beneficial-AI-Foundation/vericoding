use vstd::prelude::*;
use vstd::multiset::*;

verus! {

// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka

proof fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires 
        m.len() > 0,
    ensures 
        m.count(min) > 0,
        forall|z: int| m.count(z) > 0 ==> min <= z,
{
    assume(false);
    arbitrary()
}

// Ekki má breyta þessu falli.


///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.

// <vc-helpers>
proof fn multiset_remove_preserves_order(m: Multiset<int>, min_val: int, remaining: Multiset<int>)
    requires
        m.len() > 0,
        m.count(min_val) > 0,
        remaining == m.remove(min_val),
        forall|z: int| m.count(z) > 0 ==> min_val <= z,
    ensures
        forall|z: int| remaining.count(z) > 0 ==> min_val <= z,
{
}

proof fn multiset_to_vec_preserves_multiset(v: Vec<int>)
    requires v.len() > 0,
    ensures
        v@.to_multiset().count(v@[0]) > 0,
{
}

proof fn vec_append_preserves_sorting(v: Vec<int>, x: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] <= v@[j],
        forall|i: int| 0 <= i < v.len() ==> v@[i] <= x,
    ensures
        {
            let mut new_v = v;
            new_v.push(x);
            forall|p: int, q: int| 0 <= p < q < new_v.len() ==> new_v@[p] <= new_v@[q]
        },
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
exec fn sort(m: Multiset<int>) -> (s: Vec<int>)
    // Setjið viðeigandi ensures klausur hér
    ensures 
        s@.to_multiset() == m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut remaining = m;
    
    while remaining.len() > 0
        invariant
            result@.to_multiset().add(remaining) == m,
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result@[p] <= result@[q],
            forall|i: int, j: int| 0 <= i < result.len() && remaining.count(j) > 0 ==> result@[i] <= j,
        decreases remaining.len(),
    {
        let min_val = min_of_multiset(remaining);
        proof {
            multiset_remove_preserves_order(remaining, min_val, remaining.remove(min_val));
            vec_append_preserves_sorting(result, min_val);
        }
        result.push(min_val);
        remaining = remaining.remove(min_val);
    }
    
    result
}
// </vc-code>

fn main() {
}

}