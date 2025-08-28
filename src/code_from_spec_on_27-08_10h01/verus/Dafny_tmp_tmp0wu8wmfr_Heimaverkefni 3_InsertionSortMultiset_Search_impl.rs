use vstd::prelude::*;

verus! {

// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

proof fn subrange_properties(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures s.subrange(i, j).len() == j - i
    ensures forall|k: int| 0 <= k < j - i ==> s.subrange(i, j)[k] == s[i + k]
{
}

proof fn subrange_add_lemma(s: Seq<int>, k: int)
    requires 0 <= k <= s.len()
    ensures s == s.subrange(0, k).add(s.subrange(k, s.len() as int))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn search(s: Seq<int>, x: int) -> (k: usize)
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
        forall|z: int| s.subrange(0, k as int).contains(z) ==> z <= x,
        forall|z: int| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x,
        s == s.subrange(0, k as int).add(s.subrange(k as int, s.len() as int)),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut left: usize = 0;
    let mut right: usize = s.len();
    
    while left < right
        invariant 
            0 <= left <= right <= s.len(),
            forall|i: int| 0 <= i < left ==> s[i] <= x,
            forall|i: int| right <= i < s.len() ==> s[i] >= x
    {
        let mid = left + (right - left) / 2;
        
        if s[mid as int] <= x {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    proof {
        assert(left == right);
        assert(forall|i: int| 0 <= i < left ==> s[i] <= x);
        assert(forall|i: int| left <= i < s.len() ==> s[i] >= x);
        
        assert(forall|z: int| s.subrange(0, left as int).contains(z) ==> z <= x) by {
            let sub = s.subrange(0, left as int);
            assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == s[k]);
            assert(forall|k: int| 0 <= k < left ==> s[k] <= x);
        };
        
        assert(forall|z: int| s.subrange(left as int, s.len() as int).contains(z) ==> z >= x) by {
            let sub = s.subrange(left as int, s.len() as int);
            assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == s[left as int + k]);
            assert(forall|k: int| left <= k < s.len() ==> s[k] >= x);
        };
        
        subrange_add_lemma(s, left as int);
    }
    
    left
}
// </vc-code>

fn main() {
}

}