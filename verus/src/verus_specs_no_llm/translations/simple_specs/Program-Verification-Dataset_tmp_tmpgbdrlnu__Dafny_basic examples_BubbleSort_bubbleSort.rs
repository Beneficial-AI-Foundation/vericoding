// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Vec<int>, from: int, to: int)
 requires a != null
 reads a
 requires 0 <= from <= to <= a.Length
{
 forall u, v: : from <= u < v < to ==> a[u] <= a[v]
}


// SPEC

method bubbleSort (a: array<int>)
 requires a != null && a.Length > 0
 modifies a
 ensures sorted(a, 0, a.Length)
 ensures multiset(a[..]) == multiset(old(a[..])) -> bool {
    
}

}