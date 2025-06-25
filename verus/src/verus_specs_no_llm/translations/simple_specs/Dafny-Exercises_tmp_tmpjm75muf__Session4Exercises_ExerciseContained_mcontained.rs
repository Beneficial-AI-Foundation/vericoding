// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictSorted(s: Seq<int>) -> bool {
    forall u, w :: 0 <= u < w < s.len() ==> s.spec_index(u) < s.spec_index(w)
}

fn mcontained(v: Vec<int>, w: Vec<int>, n: int, m: int) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
    requires
        n<=m && n>=0,
        strictSorted(v.spec_index(..)),
        strictSorted(w.spec_index(..)),
        v.len() >= n && w.len() >= m
    ensures
        b==forall k:: 0<= k< n ==> v.spec_index(k) in w.spec_index(..m)//exists j :: 0 <= j < m && v.spec_index(k) == w.spec_index(j)
{
    return 0;
}

}