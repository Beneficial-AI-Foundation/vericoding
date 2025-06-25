// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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