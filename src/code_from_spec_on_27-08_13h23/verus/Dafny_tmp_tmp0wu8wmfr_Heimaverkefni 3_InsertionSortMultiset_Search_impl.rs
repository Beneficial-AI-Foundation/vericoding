use vstd::prelude::*;

verus! {

// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
fn binary_search_helper(s: Seq<int>, x: int, lo: usize, hi: usize) -> (k: usize)
    requires
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
        0 <= lo <= hi <= s.len(),
    ensures
        lo <= k <= hi,
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
    decreases hi - lo
{
    if lo == hi {
        return lo;
    }
    let mid = lo + (hi - lo) / 2;
    if s[mid] <= x {
        binary_search_helper(s, x, mid + 1, hi)
    } else {
        binary_search_helper(s, x, lo, mid)
    }
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
fn search(s: Seq<int>, x: int) -> (k: usize)
    requires
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
        forall|z: int| s.subrange(0, k as int).contains(z) ==> z <= x,
        forall|z: int| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x,
        s == s.subrange(0, k as int).add(s.subrange(k as int, s.len() as int)),
{
    binary_search_helper(s, x, 0, s.len())
}
// </vc-code>

fn main() {
}

}