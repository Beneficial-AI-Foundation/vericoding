// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn strictSorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

fn mcontained(v: Vec<int>, w: Vec<int>, n: int, m: int) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
    requires n<=m and n>=0,
             strictSorted(v[..]),
             strictSorted(w[..]),
             v.len() >= n and w.len() >= m
    ensures b==forall|k: int| 0<= k< n ==> v[k] in w[..m]//exists|j: int| 0 <= j < m and v[k] == w[j]
{
}

}