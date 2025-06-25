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

fn AllElementsEqual(a: Vec<int>, n: int) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) == n,
        !result ==> exists i :: 0 <= i < a.len() && a.spec_index(i) != n
{
    return false;
}

}