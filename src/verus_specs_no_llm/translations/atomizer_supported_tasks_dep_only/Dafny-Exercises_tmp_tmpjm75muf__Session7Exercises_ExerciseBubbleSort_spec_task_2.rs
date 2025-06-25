// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn sorted_seg(a: Vec<int>, i: int, j: int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k: : i <= l <= k < j ==> a[l] <= a[k]
}


// SPEC 


method bubbleSort(a:array<int>, c: int, f: int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a, c, f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..]) -> bool {
    
}

}