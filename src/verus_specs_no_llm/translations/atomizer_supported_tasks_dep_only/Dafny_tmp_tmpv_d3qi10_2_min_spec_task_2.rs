// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn minArray(a: Vec<int>) -> (m: int)
    requires a!= null  and a.len() > 0 ;
    ensures forall|k | 0 <= k < a.len(): int| m <= a[k],
            exists|k | 0 <= k < a.len(): int| m == a[k]
{
}

}