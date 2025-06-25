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

fn MaxA(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        forall i :: 0 <= i < a.len() ==> a.spec_index(i) <= m,
        exists i :: 0 <= i < a.len() && a.spec_index(i) == m
{
    return 0;
}

}