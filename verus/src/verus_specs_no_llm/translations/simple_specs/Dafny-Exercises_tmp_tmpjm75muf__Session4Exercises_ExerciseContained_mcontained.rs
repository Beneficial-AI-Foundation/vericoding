// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictSorted(s: Seq<int>) -> bool {
    forall |u: int, w: int| 0 <= u < w < s.len() ==> s.index(u) < s.index(w)
}

spec fn spec_mcontained(v: Vec<int>, w: Vec<int>, n: int, m: int) -> b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..]
    requires
        n<=m && n>=0,
        strictSorted(v.index(..)),
        strictSorted(w.index(..)),
        v.len() >= n && w.len() >= m
    ensures
        b==forall |k: int| 0<= k< n ==> v.index(k) in w.index(..m)//exists |j: int| 0 <= j < m && v.index(k) == w.index(j)
;

proof fn lemma_mcontained(v: Vec<int>, w: Vec<int>, n: int, m: int) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
    requires
        n<=m && n>=0,
        strictSorted(v.index(..)),
        strictSorted(w.index(..)),
        v.len() >= n && w.len() >= m
    ensures
        b==forall |k: int| 0<= k< n ==> v.index(k) in w.index(..m)//exists |j: int| 0 <= j < m && v.index(k) == w.index(j)
{
    0
}

}