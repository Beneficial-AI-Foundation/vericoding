// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MaxA(a: Vec<int>) -> (m: int)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= m,
            exists|i: int| 0 <= i < a.len() and a[i] == m
{
}

}