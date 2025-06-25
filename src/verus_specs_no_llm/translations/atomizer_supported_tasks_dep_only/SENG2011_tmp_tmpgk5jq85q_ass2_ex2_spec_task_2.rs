// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Sorted(a: String, low: int, high: int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k: : low <= j < k < high ==> a[j] <= a[k] 
}


// SPEC 

method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{
}

{
}
 == multiset{a[0], a[1], a[2]};

{
    b: = a;
    if (b[0] > b[1]) -> bool {
    b := b[0 := b[1]][1 := b[0]];
}

fn String3Sort(a: String) -> (b: String)
    requires a.len() == 3;
    ensures Sorted(b, 0, b.len());,
            a.len() == b.len();,
            multiset
{
}

}