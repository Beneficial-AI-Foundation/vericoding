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
proof fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires 
        m.len() > 0,
    ensures 
        m.count(min) > 0,
        forall|z: int| m.count(z) > 0 ==> min <= z,
{
    let mut iter = m.dom().iter();
    let first = iter.next().unwrap();
    let mut min = first;
    while let Some(z) = iter.next()
        invariant
            m.count(min) > 0,
            forall|y: int| m.count(y) > 0 && y in iter ==> min <= y,
    {
        if z < min {
            min = z;
        }
    }
    min
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
exec fn sort(m: Multiset<int>) -> (s: Vec<int>)
    ensures 
        s@.to_multiset() == m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s@[p] <= s@[q],
{
    let mut result = Vec::new();
    let mut current_multiset = m;
    
    while current_multiset.len() > 0
        invariant
            result@.to_multiset() + current_multiset == m,
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result@[p] <= result@[q],
    {
        let min_val = proof { min_of_multiset(current_multiset) };
        result.push(min_val);
        current_multiset = current_multiset.remove(min_val);
    }
    
    result
}
// </vc-code>

fn main() {
}

}